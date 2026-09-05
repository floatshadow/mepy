#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT HUP INT TERM
for input in "$root"/example/*.pratty; do
  expected=${input%.pratty}.expected
  "$root/_build/default/bin/main.exe" parse "$input" > "$actual"
  diff -u "$expected" "$actual"
done
