#!/bin/bash
# Compare optimized vs unoptimized WhileLang compilation on Livermore kernels.
# Compiles each kernel with full optimization pipeline and with -O0 (RegAlloc only),
# runs each NRUNS times, takes the minimum, and reports the speedup from optimizations.
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
PROJ_DIR="$(cd "$DIR/../.." && pwd)"
BD="$DIR/build_opt_compare"
mkdir -p "$BD"

COMPILER="$PROJ_DIR/.lake/build/bin/compiler"
if [ ! -x "$COMPILER" ]; then
  echo "Building compiler..."
  (cd "$PROJ_DIR" && lake build compiler 2>&1 | tail -1)
fi

KERNELS=(
  k01_hydro k02_iccg k03_dot k04_banded k05_tridiag
  k06_recurrence k07_eos k08_adi k09_integrate k10_diff_predict
  k11_prefix_sum k12_first_diff k13_pic_2d k14_pic_1d k15_casual
  k16_monte_carlo k17_implicit_cond k18_hydro_2d k19_linear_recurrence k20_discrete_ord
  k21_matmul k22_planck k23_hydro_implicit k24_find_min
)

# Allow running a subset: ./run_opt_compare.sh k03_dot k07_eos
if [ $# -gt 0 ]; then
  KERNELS=("$@")
fi

NRUNS=5

# ── compile all kernels ──────────────────────────────────────────
echo "Compiling kernels (optimized + unoptimized)..."
fail_opt=0; fail_noopt=0
for name in "${KERNELS[@]}"; do
  wfile="$DIR/${name}.w"
  [ -f "$wfile" ] || continue

  if "$COMPILER" "$wfile" -o "$BD/${name}_opt" 2>/dev/null; then
    :
  else
    echo "  FAIL (opt): $name"; ((fail_opt++)) || true
  fi

  if "$COMPILER" "$wfile" -O0 -o "$BD/${name}_noopt" 2>/dev/null; then
    :
  else
    echo "  FAIL (noopt): $name"; ((fail_noopt++)) || true
  fi
done
echo "Compilation done (opt failures: $fail_opt, noopt failures: $fail_noopt)"
echo ""

# ── timing helpers ───────────────────────────────────────────────
time_run() {
  python3 -c "
import subprocess, sys, time
start = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
elapsed = time.monotonic() - start
print(f'{elapsed:.3f}')
print(r.stdout, end='', file=sys.stderr)
sys.exit(r.returncode)
" "$@"
}

min_time() {
  local bin="$1" best="" out=""
  for i in $(seq 1 $NRUNS); do
    local t
    t=$(time_run "$bin" 2>"$BD/tmp_out.txt") || { echo "ERR"; return; }
    [ -z "$out" ] && out=$(cat "$BD/tmp_out.txt")
    if [ -z "$best" ] || python3 -c "exit(0 if float('$t') < float('$best') else 1)"; then
      best="$t"
    fi
  done
  echo "$best"
  echo "$out" > "$BD/tmp_last_out.txt"
}

# ── run benchmarks ───────────────────────────────────────────────
printf "\n%-22s  %10s  %10s  %10s  %s\n" \
  "Kernel" "Opt (s)" "NoOpt (s)" "Speedup" "Correct?"
printf "%-22s  %10s  %10s  %10s  %s\n" \
  "──────────────────" "────────" "────────" "────────" "────────"

log_ratios=()

for name in "${KERNELS[@]}"; do
  opt_bin="$BD/${name}_opt"
  noopt_bin="$BD/${name}_noopt"
  t_opt="—"; t_noopt="—"; speedup="—"; correct="—"
  out_opt=""; out_noopt=""

  if [ -x "$opt_bin" ]; then
    t_opt=$(min_time "$opt_bin")
    out_opt=$(cat "$BD/tmp_last_out.txt" 2>/dev/null || true)
  fi

  if [ -x "$noopt_bin" ]; then
    t_noopt=$(min_time "$noopt_bin")
    out_noopt=$(cat "$BD/tmp_last_out.txt" 2>/dev/null || true)
  fi

  # Correctness: compare opt vs noopt output
  if [ "$t_opt" != "—" ] && [ "$t_opt" != "ERR" ] && \
     [ "$t_noopt" != "—" ] && [ "$t_noopt" != "ERR" ]; then
    correct=$(python3 -c "
import re, sys
num_re = r'[-+]?[0-9]*\.?[0-9]+(?:[eE][-+]?[0-9]+)?'
def parse(text):
    d = {}
    for line in text.strip().splitlines():
        m = re.match(r'(\w+)\s*=\s*(' + num_re + r')\s*$', line)
        if m: d[m.group(1)] = m.group(2)
    return d
a, b = parse('''$out_opt'''), parse('''$out_noopt''')
shared = set(a) & set(b)
if not shared: print('—'); sys.exit()
ok = True
for k in sorted(shared):
    va, vb = float(a[k]), float(b[k])
    if va == 0 and vb == 0: continue
    if abs(va) < 1e-15 and abs(vb) < 1e-15: continue
    if abs(va - vb) / max(abs(va), abs(vb), 1e-15) >= 1e-4:
        print(f'MISMATCH {k}: {a[k]} vs {b[k]}')
        ok = False; break
if ok: print('ok')
")
  fi

  # Speedup = noopt / opt (how much faster opt is)
  if [ "$t_opt" != "—" ] && [ "$t_opt" != "ERR" ] && \
     [ "$t_noopt" != "—" ] && [ "$t_noopt" != "ERR" ]; then
    speedup=$(python3 -c "
import math
t_o, t_n = float('$t_opt'), float('$t_noopt')
if t_o > 0:
    r = t_n / t_o
    print(f'{r:.2f}x')
    print(f'{math.log(r)}', file=open('$BD/tmp_logratio.txt','w'))
else:
    print('inf')
")
    if [ -f "$BD/tmp_logratio.txt" ]; then
      log_ratios+=("$(cat "$BD/tmp_logratio.txt")")
    fi
  fi

  printf "%-22s  %10s  %10s  %10s  %s\n" \
    "$name" "$t_opt" "$t_noopt" "$speedup" "$correct"
done

# ── geometric mean ───────────────────────────────────────────────
if [ ${#log_ratios[@]} -gt 0 ]; then
  geomean=$(python3 -c "
import math
logs = [$(IFS=,; echo "${log_ratios[*]}")]
print(f'{math.exp(sum(logs)/len(logs)):.2f}x')
")
  printf "\n%-22s  %10s  %10s  %10s\n" "Geometric mean" "" "" "$geomean"
fi

rm -f "$BD/tmp_out.txt" "$BD/tmp_last_out.txt" "$BD/tmp_logratio.txt"
