#!/bin/sh

set -eu

if ! command -v typst >/dev/null 2>&1; then
  printf '%s\n' 'build: Typst is required to compile the documents.' >&2
  exit 1
fi

project_root="$(CDPATH= cd "$(dirname "$0")" && pwd)"

for source in papers/smooth-iterates.typ papers/analytic-iterates.typ presentation/slides.typ; do
  output="${source%.typ}.pdf"
  printf 'Compiling %s...\n' "$source"
  typst compile --root "$project_root" "$project_root/$source" "$project_root/$output"
done
