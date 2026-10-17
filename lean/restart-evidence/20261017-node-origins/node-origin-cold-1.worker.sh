#!/bin/bash
set -euo pipefail
export PATH=/usr/bin:$PATH
for candidate in historical-fixed-cycle base-1-0 nested-0-4-1-0 nested-8-4-8-1 nested-9-4-9-2 staggered-0-0-0 staggered-8-9-1 cross-copy-0-0-1; do
  printf 'case=%s\n' "$candidate"
  cabal exec -- runghc -Werror -package=cfta /home/tritlo/Code/mcfta/lean/restart-evidence/20261017-node-origins/node-origin-search-2.source.hs "$candidate"
done
