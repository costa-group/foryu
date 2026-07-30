#!/bin/bash

# Script to compile Solidity smart contracts in "standard JSON" format,
# obtain the CFG representation, and (as a byproduct of that same solc
# invocation, not a separate one) measure its compile time. Prints a
# filename,solc_status,solc_compile_time(ns) CSV to stdout (progress
# messages go to stderr), so a single pass produces both the _cfg folder
# and the timing data -- no need for a second, separate solc run per file.
#
# Usage (run from within benchmark/):
#   ./gen_cfg.sh 1k_most_called solc-static-linux_8_34 > ../1k_comp_time_0_8_34.csv

initial_dir="$(pwd)"
smart_contract_dir="${1:-1k_most_called}"
SOLC="${2:-solc-static-linux}"
# Output folder is tagged with the solc version actually used to compile, so
# re-running this script never silently overwrites a corpus built with a
# different solc (e.g. 1k_most_called_cfg_0_8_36).
solc_version="$("${SOLC}" --version | grep -oP 'Version: \K[0-9]+\.[0-9]+\.[0-9]+')"
solc_version_tag="${solc_version//./_}"
out_dir="${initial_dir}/${smart_contract_dir}_cfg_${solc_version_tag}"
counter=0

# settings.experimental was only introduced in solc 0.8.35 (which is also
# where yulCFGJson started requiring it); older solc rejects the key outright
# ("Unknown key \"experimental\"") and it must be omitted for them.
IFS='.' read -r solc_major solc_minor solc_patch <<< "$solc_version"
if [ "$solc_major" -gt 0 ] || { [ "$solc_major" -eq 0 ] && [ "$solc_minor" -gt 8 ]; } || { [ "$solc_major" -eq 0 ] && [ "$solc_minor" -eq 8 ] && [ "$solc_patch" -ge 35 ]; }; then
    needs_experimental=true
else
    needs_experimental=false
fi

mkdir -p "$out_dir"
cd $smart_contract_dir

echo "filename,solc_status,solc_compile_time(ns)"

find . -type f -name "*standard_input.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
    dir="${dir#./}"
    file="$(basename "$f")"
    file_no_ext="$(basename "$f" .json)"

    cd "$dir" || continue

    # Restrict outputSelection to only 'yulCFGJson', and enable
    # settings.experimental only for solc >= 0.8.35 (see above)
    python3 -c "
import json, sys
with open(sys.argv[1]) as f:
    d = json.load(f)
d['settings']['outputSelection']['*'] = {'*': ['yulCFGJson']}
d['settings'].pop('experimental', None)
if sys.argv[2] == 'true':
    d['settings']['experimental'] = True
with open(sys.argv[1], 'w') as f:
    json.dump(d, f)
" "$file" "$needs_experimental"

    out_file="${out_dir}/${dir}__${file_no_ext}_cfg.json"
    out_name="benchmark/${smart_contract_dir}_cfg_${solc_version_tag}/${dir}__${file_no_ext}_cfg.json"

    start_ns=$(date +%s%N)
    timeout 30s "${SOLC}" $file --standard-json --pretty-json > "${out_file}"
    status=$?
    end_ns=$(date +%s%N)
    elapsed_ns=$((end_ns - start_ns))

    if [ ${status} -eq 0 ]; then
        echo "${counter}) OK: $f" >&2
        echo "${out_name},OK,${elapsed_ns}"
    elif [ ${status} -eq 124 ]; then
        echo "${counter}) Timeout $f" >&2
        echo "${out_name},TIMEOUT,"
    else
        echo "${counter}) Error (${status}) $f" >&2
        echo "${out_name},ERROR,"
    fi

    cd "${initial_dir}/${smart_contract_dir}"
done
