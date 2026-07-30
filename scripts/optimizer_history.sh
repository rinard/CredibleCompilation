#!/bin/bash
# optimizer_history.sh — scan git history for each optimizer file and report:
#   1. Day introduced (relative to project start 2026-03-23)
#   2. Day finalized (last commit date, relative to project start)
#   3. Number of commits that changed the file
#   4. Last catalogued bug (from plans/bug-audit-2026-04-25.md)
#
# Rows are ordered by first appearance in the actual compiler pipeline:
#   prefixPasses:       ConstProp → DCE → CSE → (ConstProp) → DAE
#   licmClusterPasses:  LICM → (ConstProp) → ConstHoist → (CSE) → (DAE)
#   suffixPasses:       FMAFusion → (DCE) → Peephole → RegAlloc
# Each pass appears in the table once, on its FIRST appearance.
# After pipeline passes: codegen-used (non-pipeline) and disabled passes.
#
# Usage: bash scripts/optimizer_history.sh

PROJECT_START="2026-03-23"

# Convert ISO date to days since project start
days_since_start() {
    local date="$1"
    local start_secs end_secs
    start_secs=$(date -j -f "%Y-%m-%d" "$PROJECT_START" "+%s")
    end_secs=$(date -j -f "%Y-%m-%d" "${date%% *}" "+%s")
    echo $(( (end_secs - start_secs) / 86400 ))
}

# Optimizer files in EXECUTION ORDER (first-appearance in compiler pipeline).
# Format: name:filepath:bug_list:section
#   bug_list = "bug#@day,bug#@day,..." (or empty for no catalogued bugs)
#   section  = pipeline | codegen | disabled
OPTIMIZERS=(
    # Pipeline passes — first-appearance order
    # prefix: ConstProp → DCE → CSE → DAE
    "ConstPropOpt:CredibleCompilation/ConstPropOpt.lean:29a@17:pipeline"
    "DCEOpt:CredibleCompilation/DCEOpt.lean::pipeline"
    "CSEOpt:CredibleCompilation/CSEOpt.lean:24@23,25@24:pipeline"
    "DAEOpt:CredibleCompilation/DAEOpt.lean:29b@17,29c@17:pipeline"
    # LICM cluster: LICM → ConstHoist (ConstProp/CSE/DAE re-runs already shown above)
    "LICMOpt:CredibleCompilation/LICMOpt.lean:21@22,20@22,15@23:pipeline"
    "ConstHoistOpt:CredibleCompilation/ConstHoistOpt.lean::pipeline"
    # suffix: FMAFusion → Peephole → RegAlloc (DCE re-run already shown above)
    "FMAFusionOpt:CredibleCompilation/FMAFusionOpt.lean::pipeline"
    "PeepholeOpt:CredibleCompilation/PeepholeOpt.lean::pipeline"
    "RegAllocOpt:CredibleCompilation/RegAllocOpt.lean:17@20,4@20,12@22,5@25,7@26,14@26,6@26,13@27:pipeline"
    # Codegen-used (NOT in optimizer pipeline; consumed directly by ARM codegen)
    "BoundsOpt:CredibleCompilation/BoundsOpt.lean:11@29,28@29:codegen"
    "BoundsOptCert:CredibleCompilation/BoundsOptCert.lean::codegen"
    # Disabled (in tree but NOT in active pipeline — documented negative results)
    "CopyPropOpt:CredibleCompilation/CopyPropOpt.lean::disabled"
    "RematConstOpt:CredibleCompilation/RematConstOpt.lean::disabled"
)

# Get last bug from bug list "bug#@day,bug#@day,..." — picks max day
last_bug() {
    local bug_list="$1"
    if [[ -z "$bug_list" ]]; then
        echo "—"
        return
    fi
    local max_day=-1
    local max_bug=""
    IFS=',' read -ra bugs <<< "$bug_list"
    for entry in "${bugs[@]}"; do
        local bug="${entry%%@*}"
        local day="${entry##*@}"
        if (( day > max_day )); then
            max_day=$day
            max_bug=$bug
        fi
    done
    printf "bug %s (day %d)" "$max_bug" "$max_day"
}

# Print one row
print_row() {
    local name="$1" file="$2" bug_list="$3"
    local commits_log
    commits_log=$(git log --all --reverse --format='%ai' -- "$file" 2>/dev/null || echo "")
    if [[ -z "$commits_log" ]]; then
        printf "%-15s | %-22s | %-22s | %-7s | %-18s\n" "$name" "(no commits)" "-" "0" "—"
        return
    fi
    local first_date last_date commit_count first_day last_day
    first_date=$(echo "$commits_log" | sed -n '1p')
    last_date=$(echo "$commits_log" | sed -n '$p')
    commit_count=$(echo "$commits_log" | wc -l | tr -d ' ')
    first_day=$(days_since_start "$first_date")
    last_day=$(days_since_start "$last_date")
    local intro_str final_str last_bug_str
    intro_str=$(printf "day %2d (%s)" "$first_day" "${first_date%% *}")
    final_str=$(printf "day %2d (%s)" "$last_day" "${last_date%% *}")
    last_bug_str=$(last_bug "$bug_list")
    printf "%-15s | %-22s | %-22s | %-7s | %-18s\n" "$name" "$intro_str" "$final_str" "$commit_count" "$last_bug_str"
}

# Print section divider
print_divider() {
    local label="$1"
    printf "\n--- %s ---\n" "$label"
    printf "%-15s | %-22s | %-22s | %-7s | %-18s\n" "Optimizer" "Introduced" "Finalized" "Commits" "Last bug"
    printf "%-15s-+-%-22s-+-%-22s-+-%-7s-+-%-18s\n" \
        "---------------" "----------------------" "----------------------" "-------" "------------------"
}

# Iterate, grouping by section
current_section=""
for entry in "${OPTIMIZERS[@]}"; do
    IFS=':' read -r name file bug_list section <<< "$entry"
    if [[ "$section" != "$current_section" ]]; then
        case "$section" in
            pipeline) print_divider "Pipeline (first-appearance order: prefix → LICM cluster → suffix)" ;;
            codegen)  print_divider "Used by codegen (not in optimizer pipeline)" ;;
            disabled) print_divider "Disabled (not in active pipeline; documented negative results)" ;;
        esac
        current_section="$section"
    fi
    print_row "$name" "$file" "$bug_list"
done
