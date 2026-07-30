#!/bin/bash

# Regenerates the full experiment pipeline for all 3 benchmark sets
# (semanticTests, grey_stack_too_deep, 1k_most_called):
#   1) compiles each source folder into a solc-version-tagged _cfg folder,
#      measuring each file's compile time as a byproduct of that same solc
#      invocation, and expands it in place with constancy analysis
#      information (benchmark/prepare.sh, which itself calls
#      benchmark/gen_cfg.sh -- solc compiles each file exactly once, not
#      twice);
#   2) runs the liveness+constancy checker over each resulting _cfg folder
#      (run_experiments.sh).
#
# Usage (run from the repo root):
#   ./run_all.sh [solc_binary]   # defaults to solc-static-linux

set -e

SOLC="${1:-solc-static-linux}"
solc_version="$("${SOLC}" --version | grep -oP 'Version: \K[0-9]+\.[0-9]+\.[0-9]+')"
solc_version_tag="${solc_version//./_}"

echo "=== Step 1/2: compiling + timing + annotating each corpus with constancy info ==="
(cd benchmark && ./prepare.sh semanticTests "${SOLC}")
(cd benchmark && ./prepare.sh grey_stack_too_deep "${SOLC}")
(cd benchmark && ./prepare.sh 1k_most_called "${SOLC}")

echo "=== Step 2/2: running the liveness+constancy checker ==="
./run_experiments.sh "benchmark/semanticTests_cfg_${solc_version_tag}" > "semanticTests_${solc_version_tag}.csv"
./run_experiments.sh "benchmark/grey_stack_too_deep_cfg_${solc_version_tag}" > "grey_stack_too_deep_${solc_version_tag}.csv"
./run_experiments.sh "benchmark/1k_most_called_cfg_${solc_version_tag}" > "1k_most_called_${solc_version_tag}.csv"

echo "Done. Generated:"
echo "  semanticTests_comp_time_${solc_version_tag}.csv, grey_stack_too_deep_comp_time_${solc_version_tag}.csv, 1k_most_called_comp_time_${solc_version_tag}.csv"
echo "  semanticTests_${solc_version_tag}.csv, grey_stack_too_deep_${solc_version_tag}.csv, 1k_most_called_${solc_version_tag}.csv"
