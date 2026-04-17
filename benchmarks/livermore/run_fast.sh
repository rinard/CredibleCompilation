#!/bin/bash
#
# Fast smoke-test: reduced rep counts (÷1000) for quick correctness + timing check
# Creates temporary copies, builds, compares WL vs C output, shows timing.
#
# Usage:  ./run_fast.sh            — all kernels
#         ./run_fast.sh k03_dot    — one kernel
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
FAST_DIR="$SCRIPT_DIR/build_fast"
DIVISOR=1000   # divide rep counts by this

rm -rf "$FAST_DIR"
mkdir -p "$FAST_DIR/src"

# ── helpers ────────────────────────────────────────────────────

time_cmd() {
  # Prints wall-clock seconds to stdout, program output to stderr.
  # Returns the program's exit code.
  python3 -c "
import subprocess, sys, time
start = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
end = time.monotonic()
print(f'{end - start:.6f}')
print(r.stdout, end='', file=sys.stderr)
sys.exit(r.returncode)
" "$@"
}

# ── build compiler ─────────────────────────────────────────────

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building WhileLang compiler …"
  (cd "$PROJ_DIR" && lake build compiler 2>&1 | tail -1)
fi

# ── determine kernels ──────────────────────────────────────────

if [ $# -gt 0 ]; then
  KERNELS=("$@")
else
  KERNELS=()
  for f in "$SCRIPT_DIR"/k*.w; do
    KERNELS+=("$(basename "$f" .w)")
  done
fi

# ── create reduced-rep source copies ──────────────────────────

echo "Creating reduced-rep sources (÷${DIVISOR}) …"
for name in "${KERNELS[@]}"; do
  wfile="$SCRIPT_DIR/${name}.w"
  cfile="$SCRIPT_DIR/${name}.c"

  if [ -f "$wfile" ]; then
    # Replace "while (rep <= NNNN)" with reduced count
    python3 -c "
import re, sys
text = open(sys.argv[1]).read()
def reduce(m):
    n = max(1, int(m.group(1)) // $DIVISOR)
    return f'while (rep <= {n})'
text = re.sub(r'while \(rep <= (\d+)\)', reduce, text)
open(sys.argv[2], 'w').write(text)
" "$wfile" "$FAST_DIR/src/${name}.w"
  fi

  if [ -f "$cfile" ]; then
    # Replace "#define NREPS NNNN" with reduced count
    python3 -c "
import re, sys
text = open(sys.argv[1]).read()
def reduce(m):
    n = max(1, int(m.group(1)) // $DIVISOR)
    return f'#define NREPS {n}'
text = re.sub(r'#define NREPS (\d+)', reduce, text)
open(sys.argv[2], 'w').write(text)
" "$cfile" "$FAST_DIR/src/${name}.c"
  fi
done

# Copy signel.h
cp "$SCRIPT_DIR/signel.h" "$FAST_DIR/src/"

# ── compile ────────────────────────────────────────────────────

echo "Compiling …"
compile_fail=()
for name in "${KERNELS[@]}"; do
  cfile="$FAST_DIR/src/${name}.c"
  wfile="$FAST_DIR/src/${name}.w"

  if [ -f "$cfile" ]; then
    cc -O0 -o "$FAST_DIR/${name}_c_O0" "$cfile" 2>/dev/null
    cc -O2 -o "$FAST_DIR/${name}_c_O2" "$cfile" 2>/dev/null
  fi

  if [ -f "$wfile" ]; then
    if ! "$COMPILER" "$wfile" -o "$FAST_DIR/${name}_wl" 2>/dev/null; then
      compile_fail+=("$name")
    fi
  fi
done

if [ ${#compile_fail[@]} -gt 0 ]; then
  echo "  !! Compile failures: ${compile_fail[*]}"
fi

# ── run and compare ────────────────────────────────────────────

echo ""
printf "%-22s  %8s  %8s  %8s  %8s  %s\n" \
       "Kernel" "C-O0 (s)" "C-O2 (s)" "WL (s)" "WL/C-O2" "Match?"
printf "%-22s  %8s  %8s  %8s  %8s  %s\n" \
       "──────────────────" "────────" "────────" "────────" "───────" "──────"

pass=0
fail=0
skip=0

for name in "${KERNELS[@]}"; do
  t_o0="—"
  t_o2="—"
  t_wl="—"
  ratio="—"
  match="—"

  # Run C -O2 and capture output
  if [ -x "$FAST_DIR/${name}_c_O2" ]; then
    t_o2=$(time_cmd "$FAST_DIR/${name}_c_O2" 2>"$FAST_DIR/${name}_c_O2.out")
  fi
  if [ -x "$FAST_DIR/${name}_c_O0" ]; then
    t_o0=$(time_cmd "$FAST_DIR/${name}_c_O0" 2>/dev/null)
  fi

  # Run WL and capture output
  wl_ok=true
  if [ -x "$FAST_DIR/${name}_wl" ]; then
    if ! t_wl=$(time_cmd "$FAST_DIR/${name}_wl" 2>"$FAST_DIR/${name}_wl.out"); then
      wl_ok=false
    fi
  fi

  # Check WL compiled, ran with exit code 0, produced output, and values match C
  if [ -x "$FAST_DIR/${name}_wl" ]; then
    if $wl_ok && [ -f "$FAST_DIR/${name}_wl.out" ] && [ -s "$FAST_DIR/${name}_wl.out" ] \
       && [ -f "$FAST_DIR/${name}_c_O2.out" ] && [ -s "$FAST_DIR/${name}_c_O2.out" ]; then
      out_c=$(cat "$FAST_DIR/${name}_c_O2.out")
      out_w=$(cat "$FAST_DIR/${name}_wl.out")
      match=$(python3 -c "
import re, sys
c_out = '''$out_c'''
w_out = '''$out_w'''
num_re = r'[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?'
c_nums = []
for line in c_out.strip().splitlines():
    if line.startswith('elapsed'): continue
    for part in line.split('=')[1:]:
        m = re.search(num_re, part)
        if m: c_nums.append(m.group())
w_nums = []
for line in w_out.strip().splitlines():
    if '=' in line: break
    m = re.fullmatch(r'\s*(' + num_re + r')\s*', line)
    if m: w_nums.append(m.group(1))
if not c_nums or not w_nums:
    print('ok?')
    sys.exit()
n = min(len(c_nums), len(w_nums))
c_vals = [float(x) for x in c_nums[-n:]]
w_vals = [float(x) for x in w_nums[-n:]]
ok = True
for c, w in zip(c_vals, w_vals):
    if c == 0 and w == 0: continue
    if abs(c) < 1e-15 and abs(w) < 1e-15: continue
    if abs(c - w) / max(abs(c), abs(w), 1e-15) >= 1e-4:
        print(f'MISMATCH c={c} w={w}')
        ok = False; break
if ok: print('ok')
")
      if [[ "$match" == ok* ]]; then
        ((pass++))
      else
        ((fail++))
      fi
    elif ! $wl_ok; then
      match="FAIL(run)"
      ((fail++))
    else
      match="FAIL"
      ((fail++))
    fi
  elif printf '%s\n' "${compile_fail[@]}" | grep -qx "$name" 2>/dev/null; then
    match="no-wl"
    ((skip++))
  else
    match="skip"
    ((skip++))
  fi

  # Compute ratio
  if [ "$t_o2" != "—" ] && [ "$t_wl" != "—" ]; then
    ratio=$(python3 -c "print(f'{float(\"$t_wl\")/float(\"$t_o2\"):.1f}x')")
  fi

  printf "%-22s  %8s  %8s  %8s  %8s  %s\n" "$name" "$t_o0" "$t_o2" "$t_wl" "$ratio" "$match"
done

echo ""
echo "Results: $pass pass, $fail fail, $skip skip (rep counts ÷${DIVISOR})"
echo "Temp files in $FAST_DIR (delete when done)"
