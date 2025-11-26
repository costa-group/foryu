#!/bin/bash

start_dir="$(pwd)"
exit_dir="../__salida"
counter=0

find . -type f -name "*standard_input.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
    file="$(basename "$f")"
    file_no_ext="$(basename "$f" .json)"
    
    cd "$dir" || continue

    # If we need to simplify the standar-input to generate only the 'yulCFGJson'
    # python3 "${start_dir}/adapt_standard_input.py" $file "${file_no_ext}_adapted.json"
    timeout 5s "${start_dir}/solc-static-linux" $file --standard-json --pretty-json > "${start_dir}/${exit_dir}/${dir}__${file_no_ext}_cfg.json"
    if [ $? -eq 0 ]; then
        echo "${counter}) Exito: $f"
    else
        echo "${counter}) Timeout $f"
	fi

    cd "$start_dir"
done
