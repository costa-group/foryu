#!/bin/bash

# Script to compile Solidity smart contracts in "standard JSON" format and obtain the 
# CFG representation

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

find . -type f -name "*standard_input.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
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

    timeout 30s "${SOLC}" $file --standard-json --pretty-json > "${out_dir}/${dir}__${file_no_ext}_cfg.json"
    if [ $? -eq 0 ]; then
        echo "${counter}) OK: $f"
    else
        echo "${counter}) Timeout $f"
	fi

    cd "${initial_dir}/${smart_contract_dir}"
done
