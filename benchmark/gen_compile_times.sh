#!/bin/bash

# Script to measure the solc compilation time (in nanoseconds) for every
# *standard_input.json file under a benchmark source folder (e.g.
# 1k_most_called, grey_stack_too_deep, semanticTests). Originals are never
# modified: a copy is made in a temporary directory with
# `settings.experimental: true` added (required by solc to emit yulCFGJson)
# before compiling -- outputSelection is left exactly as in the original
# file; the temporary directory is removed on exit.
#
# The "filename" column reuses the same benchmark/<folder>_cfg/<addr>__<addr>_
# standard_input_cfg.json naming that gen_cfg.sh uses to name its output
# files (and that fm26.sh's --csv output already carries), so this CSV can be
# joined with those by "filename".
#
# Usage (run from within benchmark/, same convention as gen_cfg.sh):
#   cd benchmark && ./gen_compile_times.sh 1k_most_called solc-static-linux_8_34 > ../1k_comp_time_0_8_34.csv
#   cd benchmark && ./gen_compile_times.sh semanticTests > ../sem_comp_time_0_8_36.csv   # defaults to solc-static-linux

initial_dir="$(pwd)"
smart_contract_dir="${1:-1k_most_called}"
SOLC="${2:-solc-static-linux}"
# Tagged with the solc version actually used, matching gen_cfg.sh's output
# folder naming (e.g. 1k_most_called_cfg_0_8_36).
solc_version="$("${SOLC}" --version | grep -oP 'Version: \K[0-9]+\.[0-9]+\.[0-9]+')"
solc_version_tag="${solc_version//./_}"
cfg_dir_name="$(basename "${smart_contract_dir}")_cfg_${solc_version_tag}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "${tmp_dir}"' EXIT
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

echo "filename,solc_status,solc_compile_time(ns)"

cd "${smart_contract_dir}" || exit 1

find . -type f -name "*standard_input.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
    dir="${dir#./}"
    file_no_ext="$(basename "$f" .json)"

    tmp_input="${tmp_dir}/${counter}_standard_input.json"
    python3 "${initial_dir}/add_experimental.py" "$f" "${tmp_input}" "$needs_experimental"

    start_ns=$(date +%s%N)
    timeout 30s "${SOLC}" "${tmp_input}" --standard-json --pretty-json > /dev/null
    status=$?
    end_ns=$(date +%s%N)
    elapsed_ns=$((end_ns - start_ns))

    out_name="benchmark/${cfg_dir_name}/${dir}__${file_no_ext}_cfg.json"

    if [ ${status} -eq 0 ]; then
        echo "${counter}) OK: ${f}" >&2
        echo "${out_name},OK,${elapsed_ns}"
    elif [ ${status} -eq 124 ]; then
        echo "${counter}) Timeout ${f}" >&2
        echo "${out_name},TIMEOUT,"
    else
        echo "${counter}) Error (${status}) ${f}" >&2
        echo "${out_name},ERROR,"
    fi

    rm -f "${tmp_input}"
done
