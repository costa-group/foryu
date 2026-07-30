#!/bin/bash

# Prepares a full benchmark _cfg folder from a source standard-input folder:
# 1) compiles every *standard_input.json with solc into
#    <smart_contract_dir>_cfg_<solc_version>/ (via gen_cfg.sh);
# 2) expands every resulting JSON file in place with constancy analysis
#    information (analysis/constancy.py), so bin/foryu --constancy can
#    validate it directly.
#
# Usage (run from within benchmark/, same convention as gen_cfg.sh):
#   cd benchmark && ./prepare.sh semanticTests solc-static-linux_8_34
#   cd benchmark && ./prepare.sh 1k_most_called   # defaults to solc-static-linux

set -e

initial_dir="$(pwd)"
smart_contract_dir="${1:?Usage: $0 <smart_contract_dir> [solc_binary]}"
SOLC="${2:-solc-static-linux}"

./gen_cfg.sh "$smart_contract_dir" "$SOLC"

# Re-derive the exact out_dir gen_cfg.sh just wrote to (same computation, so
# it doesn't need to be scraped back out of gen_cfg.sh's progress output).
solc_version="$("${SOLC}" --version | grep -oP 'Version: \K[0-9]+\.[0-9]+\.[0-9]+')"
solc_version_tag="${solc_version//./_}"
out_dir="${initial_dir}/${smart_contract_dir}_cfg_${solc_version_tag}"

echo "Expanding ${out_dir} with constancy analysis information..."
counter=0
for f in "${out_dir}"/*.json; do
    counter=$((counter + 1))
    python3 "${initial_dir}/../analysis/constancy.py" -i "$f" -o "$f"
    echo "${counter}) constancy added: $(basename "$f")"
done
