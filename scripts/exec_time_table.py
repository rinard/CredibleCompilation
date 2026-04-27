#!/usr/bin/env python3
"""
Emit a PLDI single-column LaTeX execution-time table from a run_full.sh log.

Columns (in order):  Kernel, Axon-O, Axon, F-O0, F-O1, F-O2.
"Axon-O" = FIL-O2 (full optimization pipeline);
"Axon"   = FIL with -O0 (no optimization passes).
C columns and ratios are dropped — runtime numbers only.

Input: a log file containing run_full.sh's table lines, one per kernel:
    k01_hydro   F-O0  F-O1  F-O2  C-O0  C-O1  C-O2  WL-O0  WL-opt  ratios...

Default input is /tmp/perf_chain.log; pass --in <file> to override.

Usage:
    scripts/exec_time_table.py                       # parses /tmp/perf_chain.log
    scripts/exec_time_table.py --in /tmp/run.log
    scripts/exec_time_table.py --out plans/exec-time-pldi.tex
    scripts/exec_time_table.py --runs 5              # used in caption
"""
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
