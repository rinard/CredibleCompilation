#!/usr/bin/env python3
"""
Plot lines-of-code growth over the project's history.

For each calendar day in [start, end], picks the LATEST commit on or before
that day's end and counts Lean LOC under CredibleCompilation/ via cloc
(separating code, comment, blank). Outputs PNG + PDF.

Usage:
    scripts/loc_over_time.py [--start YYYY-MM-DD] [--end YYYY-MM-DD]
                              [--out plans/loc-over-time-pldi]
                              [--pldi]    # PLDI single-column styling

Default range: project's first month (2026-03-23 → 2026-04-23).
Default output: plans/loc-over-time (.pdf and .png).

Requires: cloc, matplotlib, git in a worktree-capable repo.
"""
import argparse, os, shutil, subprocess, sys, tempfile
from datetime import datetime, timedelta, date

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    return r

def daily_commits(start: date, end: date):
    """Return [(date, sha)] — for each day in [start, end] inclusive,
       the latest commit on or before midnight at end-of-day."""
    out = run(["git", "-C", REPO, "log", "--reverse",
               f"--since={start.isoformat()}", f"--until={(end + timedelta(days=1)).isoformat()}",
               "--format=%H %cI"], check=True)
    by_date = {}
    for line in out.stdout.strip().split("\n"):
        if not line: continue
        sha, ts = line.split(maxsplit=1)
        cdt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
        d = cdt.date()
        if start <= d <= end:
            cur = by_date.get(d)
            if cur is None or cdt > cur[0]:
                by_date[d] = (cdt, sha)
    return sorted((d, sha) for d, (_, sha) in by_date.items())

def cloc_at(sha: str, worktree: str) -> dict:
    """Checkout `sha` in `worktree` and run cloc on CredibleCompilation/."""
    run(["git", "-C", worktree, "checkout", "-q", sha], check=True)
    target = os.path.join(worktree, "CredibleCompilation")
    if not os.path.isdir(target):
        return {"blank": 0, "comment": 0, "code": 0}
    r = run(["cloc", "--csv", "--quiet", "--include-lang=Lean", target])
    for line in r.stdout.split("\n"):
        parts = line.split(",")
        # CSV format: files,language,blank,comment,code
        if len(parts) >= 5 and parts[1] == "Lean":
            try:
                return {"blank": int(parts[2]), "comment": int(parts[3]), "code": int(parts[4])}
            except ValueError:
                pass
    return {"blank": 0, "comment": 0, "code": 0}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", default="2026-03-23")
    ap.add_argument("--end",   default="2026-04-23")
    ap.add_argument("--out",   default=os.path.join(REPO, "plans", "loc-over-time"))
    ap.add_argument("--pldi",  action="store_true",
                    help="single-column PLDI styling (3.3in wide, smaller fonts)")
    args = ap.parse_args()

    start = date.fromisoformat(args.start)
    end   = date.fromisoformat(args.end)

    samples = daily_commits(start, end)
    if not samples:
        print(f"no commits in [{start}, {end}]", file=sys.stderr); sys.exit(1)
    print(f"sampling {len(samples)} commits ({start} → {end})", file=sys.stderr)

    # Use a temporary worktree so the main checkout is undisturbed.
    with tempfile.TemporaryDirectory(prefix="loc-wt-") as wt:
        run(["git", "-C", REPO, "worktree", "add", "-q", "--detach", wt, samples[0][1]], check=True)
        try:
            data = []
            for d, sha in samples:
                counts = cloc_at(sha, wt)
                data.append((d, counts))
                print(f"  {d}  {sha[:8]}  code={counts['code']:>6}  comment={counts['comment']:>5}  blank={counts['blank']:>5}",
                      file=sys.stderr)
        finally:
            run(["git", "-C", REPO, "worktree", "remove", "-f", wt])

    # Plot
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates

    dates = [d for d, _ in data]
    code = [c["code"] for _, c in data]
    comment = [c["comment"] for _, c in data]
    blank = [c["blank"] for _, c in data]
    total = [c + m + b for c, m, b in zip(code, comment, blank)]

    if args.pldi:
        plt.rcParams.update({
            "font.size": 8,
            "axes.labelsize": 8,
            "axes.titlesize": 8,
            "xtick.labelsize": 7,
            "ytick.labelsize": 7,
            "legend.fontsize": 7,
            "font.family": "serif",
        })
        fig, ax = plt.subplots(figsize=(3.3, 2.0))
    else:
        fig, ax = plt.subplots(figsize=(7.5, 4.5))

    # Stacked area: code (bottom), comment (middle), blank (top)
    ax.fill_between(dates, 0, code, label="code", alpha=0.85, color="#2b6cb0")
    ax.fill_between(dates, code, [c + m for c, m in zip(code, comment)],
                    label="comment", alpha=0.6, color="#a0aec0")
    ax.fill_between(dates, [c + m for c, m in zip(code, comment)], total,
                    label="blank", alpha=0.4, color="#cbd5e0")

    ax.set_xlabel("Date")
    ax.set_ylabel("Lines of Lean")
    ax.legend(loc="upper left", frameon=False)
    ax.xaxis.set_major_locator(mdates.WeekdayLocator(byweekday=mdates.MO))
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
    fig.autofmt_xdate(rotation=30, ha="right")
    ax.grid(True, axis="y", linestyle=":", alpha=0.5)
    ax.set_xlim(dates[0], dates[-1])
    ax.set_ylim(0, max(total) * 1.05)

    fig.tight_layout()
    png = args.out + ".png"
    pdf = args.out + ".pdf"
    fig.savefig(png, dpi=200)
    fig.savefig(pdf)
    print(f"wrote {png} and {pdf}", file=sys.stderr)

    # Also print a small CSV summary to stdout
    print("date,code,comment,blank,total")
    for d, c in data:
        t = c["code"] + c["comment"] + c["blank"]
        print(f"{d.isoformat()},{c['code']},{c['comment']},{c['blank']},{t}")

if __name__ == "__main__":
    main()
