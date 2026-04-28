#!/usr/bin/env python3
"""
Count non-blank, non-comment lines of code in each *Opt.lean file, split into
"optimization implementation" vs "certificate generation" buckets using the
file's `-- § N. <title>` section markers as boundaries.

A section is classified as `cert` when its title contains any of:
    Certificate, Cert, Expression relation, Orig-path
otherwise as `impl`. The `Main entry point` section (always small) is folded
into a separate `entry` column. Lines before the first section header
(imports, namespace, doc block) go into `prelude` and roll up into impl.

Run from anywhere; absolute paths inside.
"""

import os, re, sys
from collections import defaultdict

OPT_DIR = "/Users/mr/CredibleCompilation/CredibleCompilation"

# Files to include. RematConstOpt is an unused stub; BoundsOptCert is a
# soundness-proof file (not cert generation). Both excluded.
PASSES = [
    "DCEOpt.lean",
    "ConstPropOpt.lean",
    "ConstHoistOpt.lean",
    "CSEOpt.lean",
    "LICMOpt.lean",
    "DAEOpt.lean",
    "PeepholeOpt.lean",
    "FMAFusionOpt.lean",
    "RegAllocOpt.lean",
    "CopyPropOpt.lean",
    "BoundsOpt.lean",     # no cert section in this file
]

SECTION_RE = re.compile(r"^--\s+§\s*\d+\.\s*(.+?)\s*$")
CERT_KEYWORDS = ("Certificate", "Cert", "Expression relation", "Orig-path")
ENTRY_KEYWORDS = ("Main entry", "Entry point")

def classify(title: str) -> str:
    if any(k in title for k in ENTRY_KEYWORDS):
        return "entry"
    if any(k in title for k in CERT_KEYWORDS):
        return "cert"
    return "impl"

def count_file(path: str):
    """Return dict bucket -> ncnb LoC, plus total ncnb LoC."""
    buckets = defaultdict(int)
    in_block = False
    current = "prelude"
    with open(path) as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            stripped = line.strip()

            # Block-comment tracking. We process the line for content first
            # only when not entirely inside a block comment.
            if in_block:
                if "-/" in line:
                    in_block = False
                continue

            # Section marker — does not itself count as code.
            m = SECTION_RE.match(stripped)
            if m:
                current = classify(m.group(1))
                continue

            # Pure block-comment open (possibly multi-line).
            if stripped.startswith("/-"):
                # Closes on same line?
                if "-/" not in stripped[2:]:
                    in_block = True
                continue

            # Line comment or blank.
            if stripped == "" or stripped.startswith("--"):
                continue

            # Strip trailing line comment "-- …"; if the visible part becomes
            # empty, skip.
            idx = stripped.find("--")
            if idx >= 0:
                stripped = stripped[:idx].rstrip()
                if stripped == "":
                    continue

            buckets[current] += 1
    return buckets

def main():
    rows = []
    for fname in PASSES:
        path = os.path.join(OPT_DIR, fname)
        if not os.path.isfile(path):
            print(f"missing: {path}", file=sys.stderr)
            continue
        b = count_file(path)
        prelude = b.get("prelude", 0)
        impl = b.get("impl", 0) + prelude
        cert = b.get("cert", 0)
        entry = b.get("entry", 0)
        total = impl + cert + entry
        rows.append((fname, impl, cert, entry, total))

    # Print
    width = max(len(r[0]) for r in rows)
    print(f"{'file':<{width}}  {'impl':>6}  {'cert':>6}  {'entry':>6}  "
          f"{'total':>6}  {'%cert':>6}")
    print(f"{'-'*width}  {'-'*6:>6}  {'-'*6:>6}  {'-'*6:>6}  "
          f"{'-'*6:>6}  {'-'*6:>6}")
    sum_impl = sum_cert = sum_entry = sum_total = 0
    # Sort by total descending for readability
    rows.sort(key=lambda r: -r[4])
    for fname, impl, cert, entry, total in rows:
        cert_ratio = (100.0 * (cert + entry) / total) if total else 0.0
        print(f"{fname:<{width}}  {impl:>6}  {cert:>6}  {entry:>6}  "
              f"{total:>6}  {cert_ratio:>5.1f}%")
        sum_impl += impl; sum_cert += cert; sum_entry += entry; sum_total += total
    cert_ratio = (100.0 * (sum_cert + sum_entry) / sum_total) if sum_total else 0.0
    print(f"{'-'*width}  {'-'*6:>6}  {'-'*6:>6}  {'-'*6:>6}  "
          f"{'-'*6:>6}  {'-'*6:>6}")
    print(f"{'TOTAL':<{width}}  {sum_impl:>6}  {sum_cert:>6}  {sum_entry:>6}  "
          f"{sum_total:>6}  {cert_ratio:>5.1f}%")
    print()
    print("Bucketing rule: cert = section titles containing one of "
          "{Certificate, Cert, Expression relation, Orig-path}. "
          "entry = 'Main entry point' / 'Entry point'. "
          "impl = everything else (incl. prelude before first § marker). "
          "Excluded: RematConstOpt.lean (unused stub), "
          "BoundsOptCert.lean (soundness proofs, not cert generation).")

if __name__ == "__main__":
    main()
