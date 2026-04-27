#!/usr/bin/env python3
"""
Emit a PLDI single-column LaTeX execution-time table from a run_full.sh log.

Two modes:
  default          Kernel | Axon-O | Axon | F-O0 | F-O1 | F-O2  (raw seconds)
  --ratios         Kernel | Axon-O | F-O0 | F-O1 | F-O2 | A/F-O0 | A/F-O1 | A/F-O2
                   plus a Geomean row at the bottom for the three ratio columns.

"Axon-O" = FIL-O2 (full optimization pipeline);
"Axon"   = FIL with -O0 (no optimization passes).
C columns are always dropped.

Input: a log file containing run_full.sh's table lines, one per kernel:
    k01_hydro   F-O0  F-O1  F-O2  C-O0  C-O1  C-O2  WL-O0  WL-opt  ratios...

Default input is /tmp/perf_chain.log; pass --in <file> to override.

Usage:
    scripts/exec_time_table.py                       # default table to stdout
    scripts/exec_time_table.py --ratios              # ratios + geomean
    scripts/exec_time_table.py --in /tmp/run.log
    scripts/exec_time_table.py --out plans/exec-time-pldi.tex
    scripts/exec_time_table.py --runs 5              # used in caption
"""
import math
import argparse, os, re, sys

ROW_RE = re.compile(
    r"^(k\d+_\S+)\s+"
    r"([\d.]+|—)\s+([\d.]+|—)\s+([\d.]+|—)\s+"   # F-O0 F-O1 F-O2
    r"([\d.]+|—)\s+([\d.]+|—)\s+([\d.]+|—)\s+"   # C-O0 C-O1 C-O2
    r"([\d.]+|—)\s+([\d.]+|—)"                   # WL-O0 (Axon)  WL-opt (Axon-O)
)

def parse(path: str):
    seen = {}  # last write wins so re-runs in the same log overwrite earlier ones
    with open(path) as f:
        for line in f:
            m = ROW_RE.match(line.rstrip())
            if not m:
                continue
            name = m.group(1)
            f0, f1, f2 = m.group(2), m.group(3), m.group(4)
            wl, wlopt = m.group(8), m.group(9)
            seen[name] = (f0, f1, f2, wl, wlopt)
    return seen

def fmt(v: str) -> str:
    """Format a numeric string for LaTeX cells; pass through em-dash."""
    if v == "—" or v == "":
        return "---"
    try:
        x = float(v)
    except ValueError:
        return v
    # Two decimals; insert thin thousand-sep for the integer part if 4+ digits.
    s = f"{x:.2f}"
    if len(s.split(".")[0]) >= 4:
        ip, fp = s.split(".")
        s = f"{ip[:-3]}{{,}}{ip[-3:]}.{fp}"
    return s

# Pretty kernel names for the table — mirror the existing convention
# (escape underscores for LaTeX). k19 abbreviated to fit single-column.
def pretty_kernel(name: str) -> str:
    if name == "k19_linear_recurrence":
        name = "k19_linear_recur"
    return name.replace("_", r"\_")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in",   dest="src", default="/tmp/perf_chain.log",
                    help="run_full.sh log file (default: /tmp/perf_chain.log)")
    ap.add_argument("--out",  dest="dst", default=None,
                    help="output .tex file (default: stdout)")
    ap.add_argument("--runs", type=int, default=5,
                    help="best-of-N for caption (default: 5)")
    ap.add_argument("--ratios", action="store_true",
                    help="emit ratios table (Axon-O / F-O0,O1,O2) + geomean")
    args = ap.parse_args()

    if not os.path.exists(args.src):
        print(f"input log not found: {args.src}", file=sys.stderr); sys.exit(1)

    rows = parse(args.src)
    if not rows:
        print(f"no kernel rows parsed from {args.src}", file=sys.stderr); sys.exit(1)

    # Sort by kernel index (k01..k24)
    def kix(name: str) -> int:
        m = re.match(r"k(\d+)_", name)
        return int(m.group(1)) if m else 999
    ordered = sorted(rows.items(), key=lambda kv: kix(kv[0]))

    out = []
    if args.ratios:
        # Per-kernel ratios + geomean. 5 ratio columns:
        #   A-O/F-O0, A-O/F-O1, A-O/F-O2, A-O/Axon, Axon/A-O
        log_sums = [0.0]*5
        counts = [0]*5
        rows = []
        for name, (f0, f1, f2, wl, wlopt) in ordered:
            try:
                ao  = float(wlopt)
                ax  = float(wl)
                xs  = [float(f0), float(f1), float(f2)]
            except ValueError:
                rows.append((name, wlopt, wl, f0, f1, f2, *(["—"]*5)))
                continue
            rs = []
            # A-O / F-O{0,1,2}
            for i, x in enumerate(xs):
                if x > 0:
                    r = ao / x
                    rs.append(f"{r:.2f}")
                    log_sums[i] += math.log(r); counts[i] += 1
                else:
                    rs.append("—")
            # A-O / Axon
            if ax > 0:
                r = ao / ax;  rs.append(f"{r:.2f}")
                log_sums[3] += math.log(r); counts[3] += 1
            else:
                rs.append("—")
            # Axon / A-O
            if ao > 0:
                r = ax / ao;  rs.append(f"{r:.2f}")
                log_sums[4] += math.log(r); counts[4] += 1
            else:
                rs.append("—")
            rows.append((name, wlopt, wl, f0, f1, f2, *rs))

        gms = [f"{math.exp(s/c):.2f}" if c else "—"
               for s, c in zip(log_sums, counts)]

        out.append(r"\begin{table*}")
        out.append(r"  \centering")
        out.append(r"  \small")
        out.append(r"  \setlength{\tabcolsep}{4pt}")
        out.append(r"  \begin{tabular}{@{}l r r r r r r r r r r@{}}")
        out.append(r"    \toprule")
        out.append(r"    & \multicolumn{5}{c}{Wall-clock (s)} & \multicolumn{3}{c}{Ratio Axon-O / F-O\textit{n}} & \multicolumn{2}{c}{Axon$\leftrightarrow$Axon-O} \\")
        out.append(r"    \cmidrule(lr){2-6} \cmidrule(lr){7-9} \cmidrule(lr){10-11}")
        out.append(r"    Kernel & Axon-O & Axon & F-O0 & F-O1 & F-O2 & F-O0 & F-O1 & F-O2 & {\small Axon-O / Axon} & {\small Axon / Axon-O} \\")
        out.append(r"    \midrule")
        for (name, ao, ax, f0, f1, f2, r0, r1, r2, raxo, raxoinv) in rows:
            out.append(
                f"    {pretty_kernel(name):<26} & "
                f"{fmt(ao):>6} & {fmt(ax):>7} & "
                f"{fmt(f0):>5} & {fmt(f1):>5} & {fmt(f2):>5} & "
                f"{r0:>5} & {r1:>5} & {r2:>5} & "
                f"{raxo:>5} & {raxoinv:>5} \\\\"
            )
        out.append(r"    \midrule")
        out.append(
            f"    \\textbf{{Geomean}} & & & & & & "
            f"\\textbf{{{gms[0]}}} & \\textbf{{{gms[1]}}} & \\textbf{{{gms[2]}}} & "
            f"\\textbf{{{gms[3]}}} & \\textbf{{{gms[4]}}} \\\\"
        )
        out.append(r"    \bottomrule")
        out.append(r"  \end{tabular}")
        out.append(r"  \caption{Execution time and ratios across the canonical Livermore Loops,")
        out.append(r"           best of " + str(args.runs) + r" on Apple~M-series. Iteration counts are calibrated")
        out.append(r"           so Axon-O lands near 20\,s. ``Axon-O / F-O\textit{n}'' is the slowdown of")
        out.append(r"           our optimized verified compiler vs gfortran at level $n$ ($<$\,1 = faster).")
        out.append(r"           ``Axon-O / Axon'' shows the residual cost of optimization vs the no-opt")
        out.append(r"           verified compiler; ``Axon / Axon-O'' is the inverse and gives the speedup")
        out.append(r"           the optimization pipeline buys. F-O\textit{n} is gfortran~15.2.0.}")
        out.append(r"  \label{tab:exec-time-ratios}")
        out.append(r"\end{table*}")
    else:
        out.append(r"\begin{table}")
        out.append(r"  \centering")
        out.append(r"  \small")
        out.append(r"  \setlength{\tabcolsep}{4pt}")
        out.append(r"  \begin{tabular}{@{}l r r r r r@{}}")
        out.append(r"    \toprule")
        out.append(r"    Kernel                     &  Axon-O &     Axon &  F-O0 &  F-O1 &  F-O2 \\")
        out.append(r"    \midrule")
        for name, (f0, f1, f2, wl, wlopt) in ordered:
            out.append(
                f"    {pretty_kernel(name):<26} & "
                f"{fmt(wlopt):>7} & "
                f"{fmt(wl):>8} & "
                f"{fmt(f0):>5} & "
                f"{fmt(f1):>5} & "
                f"{fmt(f2):>5} \\\\"
            )
        out.append(r"    \bottomrule")
        out.append(r"  \end{tabular}")
        out.append(r"  \caption{Execution-time wall-clock seconds for the canonical")
        out.append(r"           Livermore Loops, best of " + str(args.runs) + r" on Apple~M-series.")
        out.append(r"           Iteration counts in each \texttt{.f}, \texttt{.c}, and")
        out.append(r"           \texttt{.w} kernel are calibrated so Axon-O lands near")
        out.append(r"           20\,s. Axon is our verified compiler at \mbox{-O0} (no")
        out.append(r"           optimization passes); Axon-O enables the full pipeline.")
        out.append(r"           F-O\textit{n} is gfortran~15.2.0. Lower is better.}")
        out.append(r"  \label{tab:exec-time}")
        out.append(r"\end{table}")

    text = "\n".join(out) + "\n"
    if args.dst:
        with open(args.dst, "w") as f:
            f.write(text)
        print(f"wrote {args.dst}", file=sys.stderr)
    else:
        sys.stdout.write(text)

if __name__ == "__main__":
    main()
