set -eu
export PATH=/usr/bin:$PATH
cabal test cfta:test:unit-tests --test-show-details=direct --test-options="--seed=20261027 +RTS -N1 -RTS" -j1
fourmolu --mode check cfta/src/Data/CFTA/EGraph.hs cfta/test/Data/CFTA/EGraphSpec.hs
cabal-gild --input cfta/cfta.cabal --mode check
