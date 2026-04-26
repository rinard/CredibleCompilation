#!/usr/bin/env python3
"""
Count lines of Lean source by construct kind across the project.

Walks all .lean files under the given roots, classifies each top-level
construct by its keyword (theorem/lemma/def/etc.), and reports total
lines per kind. Lines belonging to a construct = lines between its
opening keyword and the next top-level keyword (or EOF).

Lines outside any construct (imports, namespace/section, blank lines,
top-level comments) are bucketed as "other".

Usage:
    scripts/loc_by_kind.py [paths ...]
    scripts/loc_by_kind.py --by-file  # also break down per file
    scripts/loc_by_kind.py --latex    # emit LaTeX table

If no paths given, defaults to CredibleCompilation/.
"""
import argparse, os, re, sys
from collections import defaultdict

# Top-level construct openers we care about. Order matters: more specific
# (e.g., "private partial def") matches before less specific ("def").
KIND_PATTERNS = [
    ("private partial def",   re.compile(r"^private\s+partial\s+def\b")),
    ("private noncomputable def", re.compile(r"^private\s+noncomputable\s+def\b")),
    ("private theorem",       re.compile(r"^private\s+theorem\b")),
    ("private lemma",         re.compile(r"^private\s+lemma\b")),
    ("private def",           re.compile(r"^private\s+def\b")),
    ("partial def",           re.compile(r"^partial\s+def\b")),
    ("noncomputable def",     re.compile(r"^noncomputable\s+def\b")),
    ("theorem",               re.compile(r"^theorem\b")),
    ("lemma",                 re.compile(r"^lemma\b")),
    ("def",                   re.compile(r"^def\b")),
    ("abbrev",                re.compile(r"^abbrev\b")),
    ("inductive",             re.compile(r"^inductive\b")),
    ("structure",             re.compile(r"^structure\b")),
    ("class",                 re.compile(r"^class\b")),
    ("instance",              re.compile(r"^instance\b")),
    ("opaque",                re.compile(r"^opaque\b")),
    ("axiom",                 re.compile(r"^axiom\b")),
    ("example",               re.compile(r"^example\b")),
]

def classify(line: str) -> str | None:
    """If line is a top-level construct opener, return its kind. Else None."""
    for kind, pat in KIND_PATTERNS:
        if pat.match(line):
            return kind
    return None

def is_code_line(line: str, depth: int) -> tuple[bool, int]:
    """Decide whether `line` contains non-blank, non-comment content.
    Tracks nested `/- ... -/` block comments via depth (carried across lines).
    Returns (is_code, new_depth)."""
    has_code = False
    i = 0
    n = len(line)
    while i < n:
        if depth > 0:
            j = line.find("-/", i)
            if j == -1:
                return (has_code, depth)
            i = j + 2
            depth -= 1
            continue
        if i + 1 < n:
            two = line[i:i+2]
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "--":
                break  # rest of line is a line comment
        c = line[i]
        if not c.isspace():
            has_code = True
        i += 1
    return (has_code, depth)

def count_file(path: str) -> dict[str, int]:
    """Return {kind: code_lines} — only non-blank, non-comment lines counted.
    Each code line is attributed to the most recent top-level construct
    (or 'other' if none has been seen yet)."""
    counts: dict[str, int] = defaultdict(int)
    current_kind: str | None = None
    block_depth = 0
    with open(path, encoding="utf-8") as f:
        for raw in f:
            line = raw.rstrip("\n")
            # The construct opener itself is detected before deciding
            # is-code: openers like "def foo := ..." are always code lines.
            kind = classify(line) if block_depth == 0 else None
            if kind is not None:
                current_kind = kind
            is_code, block_depth = is_code_line(line, block_depth)
            if is_code:
                counts[current_kind or "other"] += 1
    return dict(counts)

def walk_lean_files(roots: list[str]) -> list[str]:
    found = []
    for root in roots:
        if os.path.isfile(root) and root.endswith(".lean"):
            found.append(root)
        elif os.path.isdir(root):
            for dirpath, dirnames, filenames in os.walk(root):
                # Skip build artifacts
                dirnames[:] = [d for d in dirnames if d not in (".lake", "build", ".git")]
                for fn in filenames:
                    if fn.endswith(".lean"):
                        found.append(os.path.join(dirpath, fn))
    return sorted(found)

# Display order: type/data, defs, then proofs, then other
DISPLAY_ORDER = [
    "inductive", "structure", "class", "abbrev",
    "def", "private def", "partial def", "private partial def",
    "noncomputable def", "private noncomputable def",
    "instance", "opaque", "axiom", "example",
    "theorem", "private theorem", "lemma", "private lemma",
    "other",
]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="*", default=["CredibleCompilation"])
    ap.add_argument("--by-file", action="store_true", help="also print per-file breakdown")
    ap.add_argument("--latex", action="store_true", help="emit LaTeX table")
    args = ap.parse_args()

    files = walk_lean_files(args.paths)
    if not files:
        print(f"no .lean files found under {args.paths}", file=sys.stderr); sys.exit(1)

    total: dict[str, int] = defaultdict(int)
    per_file: dict[str, dict[str, int]] = {}
    for path in files:
        counts = count_file(path)
        per_file[path] = counts
        for k, v in counts.items():
            total[k] += v

    grand_total = sum(total.values())

    kinds_seen = [k for k in DISPLAY_ORDER if k in total]
    extras = sorted(k for k in total if k not in DISPLAY_ORDER)
    kinds_seen.extend(extras)

    if args.latex:
        print(r"\begin{tabular}{@{}l r r@{}}")
        print(r"  \toprule")
        print(r"  Kind & LOC & \% \\")
        print(r"  \midrule")
        for k in kinds_seen:
            v = total[k]
            pct = 100.0 * v / grand_total
            print(f"  {k.replace('_', r'\_')} & {v:,} & {pct:.1f} \\\\")
        print(r"  \midrule")
        print(f"  \\textbf{{Total}} & \\textbf{{{grand_total:,}}} & 100.0 \\\\")
        print(r"  \bottomrule")
        print(r"\end{tabular}")
    else:
        print(f"{'Kind':<28} {'LOC':>8} {'%':>6}")
        print("-" * 46)
        for k in kinds_seen:
            v = total[k]
            pct = 100.0 * v / grand_total
            print(f"{k:<28} {v:>8,} {pct:>5.1f}%")
        print("-" * 46)
        print(f"{'TOTAL':<28} {grand_total:>8,}")

    if args.by_file:
        print()
        print(f"{'File':<60} {'LOC':>7}")
        print("-" * 70)
        for path in sorted(per_file):
            print(f"{path:<60} {sum(per_file[path].values()):>7,}")

if __name__ == "__main__":
    main()
