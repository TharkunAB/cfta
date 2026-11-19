#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 3 ] || [ "$#" -gt 4 ]; then
    echo "Usage: $0 CURSOR_CHECKOUT TOKENIZER_JSON OUTPUT_DIRECTORY [bench]" >&2
    exit 2
fi
spike=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
checkout=$(realpath "$1")
tokenizer=$(realpath "$2")
mkdir -p "$3"
output=$(cd "$3" && pwd)
mkdir -p "$output/build"
cursor="$output/build/cursor"
export PYTHONHASHSEED=0
py() { uv run --no-project --python 3.12 python "$@"; }

(
    cd "$checkout"
    cabal build cfta-generator:exe:pre3-cfta --enable-optimization=2 -j1
    cabal exec --enable-optimization=2 -- ghc -O2 -Wall -Werror -rtsopts \
        -package cfta -package cfta-generator -outputdir "$output/build" -o "$cursor" "$spike/CursorPrefilter.hs"
)
"$cursor" SELFTEST +RTS -M3G
py "$spike/fixture.py" "$tokenizer" "$output"
vocab="$output/vocab.tsv"

for notation in infix prefix; do
    prefixes="$output/$notation-exhaustive.txt"
    candidates="$output/$notation-structural.csv"
    py "$spike/mask.py" "$notation" 7 "$vocab" "$prefixes" verify --oracle "$candidates"
    "$cursor" "$notation" 7 "$vocab" "$prefixes" - MASK +RTS -M3G > "$output/$notation-baseline.csv"
    "$cursor" "$notation" 7 "$vocab" "$prefixes" "$candidates" MASK +RTS -M3G > "$output/$notation-filtered.csv"
    cmp "$output/$notation-baseline.csv" "$output/$notation-filtered.csv"
done

# Cold control: run the syntax stage before the CFTA process and compare each row.
prefixes="$output/prefix-15.txt"
candidates="$output/prefix-15-structural.csv"
all="$output/prefix-15-all.csv"
ids=$(cut -f1 "$vocab" | paste -sd, -)
awk -v ids="$ids" '{print ids}' "$prefixes" > "$all"
for mode in baseline filtered all; do
    case "$mode" in
        baseline) selection=- ;;
        filtered) selection="$candidates" ;;
        all) selection="$all" ;;
    esac
    echo "prefix size=15 cold $mode"
    {
        time {
            if [ "$mode" = filtered ]; then
                py "$spike/mask.py" prefix 15 "$vocab" "$prefixes" mask > "$candidates"
            fi
            "$cursor" prefix 15 "$vocab" "$prefixes" "$selection" MASK +RTS -M3G
        }
    } > "$output/prefix-15-$mode-final.csv"
done
cmp "$output/prefix-15-baseline-final.csv" "$output/prefix-15-filtered-final.csv"
cmp "$output/prefix-15-baseline-final.csv" "$output/prefix-15-all-final.csv"

if [ "${4:-}" = bench ]; then
    for cell in "infix 7" "prefix 7" "prefix 15"; do
        read -r notation size <<< "$cell"
        prefixes="$output/$notation-$size.txt"
        candidates="$output/$notation-$size-structural.csv"
        py "$spike/mask.py" "$notation" "$size" "$vocab" "$prefixes" mask > "$candidates"
        for trial in 1 2 3; do
            echo "$notation size=$size trial=$trial baseline"
            "$cursor" "$notation" "$size" "$vocab" "$prefixes" - 2000 +RTS -M3G
            echo "$notation size=$size trial=$trial filtered"
            "$cursor" "$notation" "$size" "$vocab" "$prefixes" "$candidates" 2000 +RTS -M3G
            py "$spike/mask.py" "$notation" "$size" "$vocab" "$prefixes" indexed --repeats 2000
        done
    done
fi
