set -eu
export PATH=/usr/bin:$PATH
cabal test cfta:test:unit-tests --test-show-details=direct --test-options="--seed=20261027 +RTS -N1 -RTS" -j1
cabal exec -- runghc -package=cfta /tmp/mcfta-flat-native-assimilation-20261027/extract-context-repro.hs > /tmp/mcfta-flat-native-assimilation-20261027/extract-context-output.txt
cat /tmp/mcfta-flat-native-assimilation-20261027/extract-context-output.txt
fourmolu --mode check cfta/src/Data/CFTA.hs cfta/src/Data/CFTA/EGraph.hs cfta/src/Data/CFTA/Internal/Tree.hs cfta/test/Data/CFTA/EGraphSpec.hs
cabal-gild --input cfta/cfta.cabal --mode check
