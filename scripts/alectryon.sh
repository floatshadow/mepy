#!/usr/bin/env bash

set -euo pipefail

while IFS= read -r -d '' file; do
  outdir="html/$(dirname "$file")"
  mkdir -p "$outdir"

  echo "Rendering $file"

  opam exec -- alectryon \
    --coq-driver vsrocq \
    --frontend coqdoc \
    --backend webpage \
    --output-directory "$outdir" \
    --cache-directory .alectryon-cache \
    --long-line-threshold 0 \
    "$file"

done < <(find theories -type f -name '*.v' -print0)

if [[ -f README.md ]]; then
  {
    # MyST should treat chapter links as URLs, not document cross-references.
    printf '%s\n' '---' 'myst:' '  all_links_external: true' '---' ''
    # Keep source links in README.md; point the homepage at HTML chapters.
    sed -E 's@\]\((theories/[^)]*)\.v\)@](\1.html)@g' README.md
  } |
    opam exec -- alectryon \
      --frontend md \
      --backend webpage \
      --stdin-filename README.md \
      --output html/index.html \
      --output-directory html \
      --long-line-threshold 0 \
      -
fi
