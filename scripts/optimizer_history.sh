#!/bin/bash
# optimizer_history.sh — scan git history for each optimizer file and report:
#   1. Day introduced (relative to project start 2026-03-23)
#   2. Day finalized (last commit date, relative to project start)
#   3. Number of commits that changed the file
#   4. Last catalogued bug (from plans/bug-audit-2026-04-25.md)
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

# Optimizer files in the codebase
# Format: name:filepath:bug_list (bug_list is "bug#@day,bug#@day,..." — last bug used)
OPTIMIZERS=(
    "ConstPropOpt:CredibleCompilation/ConstPropOpt.lean:29a@17"
    "DCEOpt:CredibleCompilation/DCEOpt.lean:"
    "DAEOpt:CredibleCompilation/DAEOpt.lean:29b@17,29c@17"
    "CSEOpt:CredibleCompilation/CSEOpt.lean:24@23,25@24"
    "LICMOpt:CredibleCompilation/LICMOpt.lean:21@22,20@22,15@23"
    "ConstHoistOpt:CredibleCompilation/ConstHoistOpt.lean:"
    "PeepholeOpt:CredibleCompilation/PeepholeOpt.lean:"
    "RegAllocOpt:CredibleCompilation/RegAllocOpt.lean:17@20,4@20,12@22,5@25,7@26,14@26,6@26,13@27"
    "BoundsOpt:CredibleCompilation/BoundsOpt.lean:11@29,28@29"
    "BoundsOptCert:CredibleCompilation/BoundsOptCert.lean:"
    "FMAFusionOpt:CredibleCompilation/FMAFusionOpt.lean:"
    "CopyPropOpt:CredibleCompilation/CopyPropOpt.lean:"
    "RematConstOpt:CredibleCompilation/RematConstOpt.lean:"
)

# Get last bug from bug list "bug#@day,bug#@day,..." — picks max day
last_bug() {
    local bug_list="$1"
    if [[ -z "$bug_list" ]]; then
        echo "—"
        return
    fi
    # Split on comma, find max day, format as "bug#@day"
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

# Header
printf "%-15s | %-22s | %-22s | %-7s | %-18s\n" "Optimizer" "Introduced" "Finalized" "Commits" "Last bug"
printf "%-15s-+-%-22s-+-%-22s-+-%-7s-+-%-18s\n" \
    "---------------" "----------------------" "----------------------" "-------" "------------------"

# For each optimizer, query git
for entry in "${OPTIMIZERS[@]}"; do
    IFS=':' read -r name file bug_list <<< "$entry"

    # Get all commits touching this file (oldest first)
    commits_log=$(git log --all --reverse --format='%ai' -- "$file" 2>/dev/null || echo "")

    if [[ -z "$commits_log" ]]; then
        printf "%-15s | %-22s | %-22s | %-7s | %-18s\n" "$name" "(no commits)" "-" "0" "—"
        continue
    fi

    first_date=$(echo "$commits_log" | sed -n '1p')
    last_date=$(echo "$commits_log" | sed -n '$p')
    commit_count=$(echo "$commits_log" | wc -l | tr -d ' ')

    first_day=$(days_since_start "$first_date")
    last_day=$(days_since_start "$last_date")

    intro_str=$(printf "day %2d (%s)" "$first_day" "${first_date%% *}")
    final_str=$(printf "day %2d (%s)" "$last_day" "${last_date%% *}")
    last_bug_str=$(last_bug "$bug_list")

    printf "%-15s | %-22s | %-22s | %-7s | %-18s\n" "$name" "$intro_str" "$final_str" "$commit_count" "$last_bug_str"
done
