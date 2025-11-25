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

    timeout 5s "${start_dir}/solc-static-linux" $file --standard-json --pretty-json > "${start_dir}/${exit_dir}/${dir}__${file_no_ext}_cfg.json"
    if [ $? -eq 0 ]; then
        echo "${counter}) Exito: $f"
    else
        echo "${counter}) Timeout $f"
	fi

    cd "$start_dir"
done
