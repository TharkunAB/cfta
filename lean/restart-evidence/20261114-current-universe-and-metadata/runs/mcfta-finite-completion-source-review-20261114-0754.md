# Source review: repeated recursion and finite completion

Result: unresolved. No supported counterexample or Haskell defect was established. The actual clear operation retains the node and union-find aliases. It removes the suspended-path bucket. Local clear, restart and marker emission therefore do not, by themselves, establish a common finite completion of the original obligations.

## Actual path

`Synthesis.solutionsOfSize` → `orderedSearchSpace` → `programsIn` → `runsBy` → `runsFrom` → `initEnumerationState` → `enumerateFully` → `enumerateUntil'`. The raw fixture instead passes the SAME genuine `rawSearchSpace` to `Space root (const 0)`, before reduction/refolding. It uses the existing worker.

Enumeration.hs287–293 keys recursion by node identity and the SET of suspended path tries. The key omits their target UVars, multiplicities and order. At1001–1012, a selected repeated recursive boundary is rewritten to `UVarUnenumerated (Just n) Sequence.Empty`; the worker restarts without either oracle callback. The write430–468 retains union-find and ancestry and updates the expandable and waiting indexes. The slot is disabled because a recursive boundary with no SCS is not expandable473. The scheduler828–877 rejects remaining work when every expandable slot is blocked. The real next tag is ExpansionDone when there are no candidates; ExpansionStuck ends the branch.

Terminal paths are merged into union-find classes at Enumeration.hs725–753. Assimilation490–511 preserves their class ancestry. Edge preparation769–781 checks inherited required-child availability before distributing paths. These operations can exclude an infinite type equation before the clear branch is entered. They are relevant evidence; they are not an existing proof that every eventual clear is safe for joint finite completion.

The Haskell emitters1057–1082 replace any pending recursive boundary with the requested recursion marker; they do not construct a finite term in that node's language. `runsFrom`1285–1293 returns the rendered term and residual pairs from one run. `Synthesis.programsIn`969–970 discards the residual list and erases type children with `toProgram`963–966.

The Lean implementation matches this boundary: Recursion.checkRepeated17–29 clears the same bucket; SelectedStep.runPrefixWithNarrow54–63 returns parked and uses ParkedRestart.adapt95–101 to rebuild indexes; Restart.run24–29 rejects stuck selection. Rendering.expandFragment28–43 and expandUVar45–55 emit the marker at recursive boundaries. None of those bodies produces a shared finite type witness.

The exact existing meaning law is ParkedLanguage.checkRepeated_true_satisfies68–78: pre-state assignment satisfaction is equivalent to post-state satisfaction AND the original removed bucket's Suspended.Holds facts. Its assignment is fixed. The law does not infer those removed facts from the post-state alone. The flat law RecursionMeaning35–48 retains the same conjunction. This is the first missing semantic inference at clearing; it must be derived from the actual reachable source history, not supplied as another premise.

## Provenance is separate

CurrentUniverseOrigins.firstOrderRaw_overUniverse62–65 derives OverUniverse for the actual returned raw expression. UniverseOrigins.binder_eq32–35 identifies any binder in that prefix with the captured type universe. Haskell allTypes475–481 constructs an unconstrained recursive universe with arrow, four variable leaves and the catalog constructors. Generalization524–531 puts equality classes in the surrounding finite type prefix.

This provenance restricts the original recursive nodes. It does not yet identify all later native intersection handles with that original binder, prove absence of relevant recurrence, or produce one finite assignment for all aliases. Individual nonempty type nodes can still participate in an impossible joint equation. This review does not infer a shared witness from independent node witnesses or from equal Mu markers.

## What the retained SKI result says

The exact source fixture is `/tmp/mcfta-source-raw-ski-check-20261113-1918/`. Probe.hs58–60/73–78 constructs the FirstOrder library sink, s, i, k; query Bool; size4. Raw-SKI.txt18–35 records 175 complete public results and 175 complete typed results from SEPARATE calls. Both lists exhausted. `sink (s i i)` is absent; `sink (s k k)` is present. The positive typed pair and its empty residual list were retained together. These are not 175 Lean fuel outcomes.

Raw-SKI.txt16 says reachesConstrainedMu=False. That flag controls the merge-time provablyEmpty shortcut; the repeated-boundary check itself is not conditional on the flag. The log does not count clear/park entries. Therefore neither the negative result nor the positive control establishes that a relevant repeated-clear case was exercised. The absent program would require an occurs equation a = a -> b. The result is useful actual-source evidence, but it does not decide the universal finite-completion question.

## Small exact supported follow-up, NOT RUN

Use FirstOrder library entries `need :: (a -> F a) -> Bool`, `i :: b -> b`, `liftF :: c -> F c`; no argument-only groups, avoid groups or query bindings; goal Bool; size2. This is the existing source generator API, not an arbitrary automaton or caller. `need i` forces a = F a and has no finite first-order type. `need liftF` is a finite positive control. The constructor catalog includes unary F because it occurs in these actual library schemes.

Root can use its serial capped runner to start the existing Nix/Cabal environment, for example:

```sh
nix-shell --expr 'let pkgs = import <nixpkgs> {}; in pkgs.mkShell { inputsFrom = [ (import ./shell.nix { inherit pkgs; }) ]; packages = [ pkgs.gmp ]; }' --run 'cabal repl cfta-generator:lib:cfta-generator --offline --repl-options=-ignore-dot-ghci'
```

The exact GHCi input is:

```haskell
:set -XOverloadedStrings
import qualified Data.CFTA.Gen.Synthesis as S
import qualified Data.CFTA.Enumeration as E
let a = S.TVar "a"
let b = S.TVar "b"
let c = S.TVar "c"
let f t = S.TCons "F" [t]
let bool = S.TCons "Bool" []
let fun x y = S.TFun x y
let lib = S.Library [("need",fun (fun a (f a)) bool,["need"]),("i",fun b b,["i"]),("liftF",fun c (f c),["liftF"])] [] [] S.FirstOrder
let query = S.Query [] bool
let root = S.rawSearchSpace lib query 2
E.reachesConstrainedMu root
let rawPrograms = S.programsIn (S.Space root (const 0))
let defaultPrograms = S.solutionsOfSize lib query 2
let bad = S.App (S.Var "need") (S.Var "i")
let good = S.App (S.Var "need") (S.Var "liftF")
(length rawPrograms, bad `elem` rawPrograms, good `elem` rawPrograms)
(length defaultPrograms, bad `elem` defaultPrograms, good `elem` defaultPrograms)
```

Each scheme uses a distinct actual variable name, a/b/c. This avoids the known cross-component repeated-name frontend confound. Expected membership is False/True on BOTH routes; no result is claimed. Log reachesConstrainedMu for the genuine raw SourceOnly root; do not infer it from the previous SKI result. Record negative presence and control presence independently of completed finite-list exhaustion. Record a timeout separately; it gives no absence claim. The length expression forces complete enumeration, so Root should use a tiny external timeout for each route. Reuse the existing paired typed-run logging to retain each observed typed term and its own residuals. An observed bad program would establish an actual supported failure. Its absence would settle this case only. To determine whether clearing caused the outcome, an additional Root-owned temporary trace must distinguish the exact1006–1012 clear branch from ExpansionStuck and merge rejection. The unchanged worker must remain the authority; no alternate worker or oracle policy is proposed. An oracle-only trace misses clearing because that branch bypasses the oracle.

No child compiler, evaluation/runtime job, live write, Git or board action ran. This report is the only new file. No Haskell change was made or proposed as a fix. Existing failures and unknown historical exposure remain unchanged. Pins below identify consulted files; they do not certify a complete global source-view union. Two broad filename searches included retained-evidence paths and truncated filename-only output; no semantic claim uses those listings. No new source body was acquired from those historical copies.

## Current pins

Whole-file hashes identify each original; they do not imply complete semantic review. Semantic views used the named declarations and ranges above; cuts also exposed some short modules in full. This report does not reset prior source accounting or certify a global exposure union. Fixture source/log identity is retained separately from current source identity. Current package files were hashed without Git. Existing runtime evidence was read; it was not repeated.

- `cfta/src/Data/CFTA/Enumeration.hs`: 1595L/71733B, SHA256 `26236dc68be7019b28c10d4b42d1bbecf89f9145c41bad7977fc177332b597f8`.
- `cfta-generator/src/Data/CFTA/Gen/Synthesis.hs`: 1007L/45608B, SHA256 `abbd34f76d87164cdedfc63bd96fe771efe16686711ff723485982de752a2c0d`.
- `lean/MicroCFTA/SourcePruningEnumerationRecursion.lean`: 229L/16112B, SHA256 `14cb1702701b110366170500ac722cdeeb7a04d61fd09928634dbf6b9db76850`.
- `lean/MicroCFTA/SourcePruningEnumerationParkedRestart.lean`: 253L/16903B, SHA256 `bf5c16846f77bfa8d146f58ea8dafbde34ca1a1bef9dbfe453f344bebc0b94e0`.
- `lean/MicroCFTA/SourcePruningEnumerationRestart.lean`: 81L/5022B, SHA256 `eb236a511d3ccd26acfdc52558803eb8f53d287ddca9a444a6e31823d87c9526`.
- `lean/MicroCFTA/SourcePruningEnumerationSelectedStep.lean`: 257L/16408B, SHA256 `94eef7250dc271996ad9da0e714616124e97773b2ab88c796939cd55656379ba`.
- `lean/MicroCFTA/SourcePruningEnumerationParkedLanguage.lean`: 127L/7503B, SHA256 `525d06544983b6527d8490604ec5e5fb3fc87c3ec10b53be731713738fb8e385`.
- `lean/MicroCFTA/SourceFlatPruningRecursionMeaning.lean`: 65L/3666B, SHA256 `35242b82ec24f0288bf51309e5c0a655039ba6fe39254a7b5410efc8e85fca81`.
- `lean/MicroCFTA/SourcePruningEnumerationRendering.lean`: 204L/12991B, SHA256 `6dfeb5bee518f86b60bfe16edb057c95820700610a8805ba982b3539ec1b458b`.
- `lean/MicroCFTA/SourceSynthesisCurrentUniverseOrigins.lean`: 97L/4464B, SHA256 `faf9fa6464a38ed1bfba269c4dbc063cc4132197e7e5212263a835670dcad61a`.
- `lean/MicroCFTA/SourceSynthesisUniverseOrigins.lean`: 426L/21524B, SHA256 `1c1c5e91511dea6c571b14ac040e2cdb1152941a4136c6cf82ec6cc2ab4b705f`.
- `/tmp/mcfta-source-raw-ski-check-20261113-1918/Probe.hs`: 185L/8031B, SHA256 `0bb459f076701f86536846e073b2be6ae001d905d951fa269a81ff1400489585`.
- `/tmp/mcfta-source-raw-ski-check-20261113-1918/DefaultProbe.hs`: 187L/8191B, SHA256 `74d27515297a6175c6e61017ba3b866051e8ce449e0984d1c949c17aa0fe8a75`.
- `/tmp/mcfta-source-raw-ski-check-20261113-1918/raw-SKI.txt`: 35L/2962B, SHA256 `02a40404cc09a2f0dde4c6ddd9ec5908c64dc4b27c00270e8f68e1785c9114e9`.
- `/tmp/mcfta-source-raw-ski-check-20261113-1918/checked.json`: 82L/3040B, SHA256 `673d8352984791185308873b34527673da7505b998a48bbbe7d27d8e1e1d559a`.
