#!/bin/bash

start_dir="$(pwd)"
exit_dir="../__salida"
counter=0

find . -type f -name "*.json" -print0 | while IFS= read -r -d '' f; do
    counter=$((counter + 1))
    dir="$(dirname "$f")"
    file="$(basename "$f")"

    cd "$dir" || continue

	# inicio=$(date +%s%N)
    # solc $file --standard-json --pretty-json > "${start_dir}/${exit_dir}/${file}_cfg.json"
    # fin=$(date +%s%N)
    # duracion_ns=$((fin - inicio))
    # duracion_ms=$((duracion_ns / 1000000))
    # echo "${counter}) ${duracion_ms} ms"
    # echo "$f"
    # echo 

    timeout 5s "${start_dir}/solc-static-linux" $file --standard-json --pretty-json > "${start_dir}/${exit_dir}/${file}_cfg.json"
    if [ $? -eq 0 ]; then
        echo "${counter}) Exito: $f"
    else
        echo "${counter}) Timeout $f"
	fi

    cd "$start_dir"
done
