#!/usr/bin/env bash
set -e
cd /home/tritlo/Code/mcfta
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- ghci -ignore-dot-ghci -v0 -package=cfta -package=cfta-generator' <<'HS'
:set -XOverloadedStrings
import Data.CFTA.Gen.Synthesis
import Data.CFTA.Equality
import Data.CFTA.Symbol (Symbol)
import qualified Data.CFTA.Term as T
import Control.Exception (evaluate)
import System.Timeout (timeout)
let a=TVar "a"; b=TVar "b"; c=TVar "c"; int=TCons "Int" []; lib=Library [("f",TFun (TFun a a) b,["f"]),("g",TFun c (TFun c c),["g"])] [] [] FirstOrder; q=Query [] int; raw=rawSearchSpace lib q 2; space=reduceWithOrder raw
let report tag text = do { result <- timeout 3000000 (evaluate (length text)); putStrLn (tag ++ case result of { Nothing -> ": TIMEOUT"; Just _ -> ": " ++ text }) }
report "raw/noStop typed runs" (show (take 16 (runs "Mu" raw)))
report "reduced/noStop typed runs" (show (take 16 (runsBy (spaceOrder space) "Mu" (spaceNode space))))
report "public programs" (show (take 16 (solutionsOfSize lib q 2)))
let i=T.Node "Int" [] :: T.Term Symbol; marker=T.Node "(->)" []; arr x y=T.Node "->" [marker,x,y]; s=arr i i; ff=T.Node "filter" [i,T.Node "app" [i,marker,T.Node "f" [arr (arr s s) i],T.Node "f" [arr s s]]]
report "finite f-f control accepted by same raw root" (show (accepts raw ff))
:quit
HS
