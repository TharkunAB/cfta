# Native cached selection

## Current result

Proof commit: `805aa57cf3dc5df066010194ae74ef3396c222ec`.
Source: `MicroCFTA/SourcePruningEnumerationSelection.lean`.
Source SHA-256: `f90690fbe6b04bca3c8639c52789a049e87ed619964d857dfa91efe5201eb7b9`.
The source has 114 lines. It adds four theorems and no runtime definition.

`offered` consumes the actual `EnumerationPureSelection.next` result.
It gives allocated range membership, a true candidate flag and no waiting
entry. The existing preference rule rejects invalid hints and falls back
to the first offered variable.

`unblocked_avoids` uses exact canonical waiting counts and finite root
paths. An unblocked root has a class separate from every suspended
reference in every stored pending bucket. The result applies to any stored
slot, not only the selected slot.

`ready` adds `Safe` and the actual native candidate flag equation.
The true flag excludes elimination. `LiveRoots` then gives rootness.
The waiting result supplies `Avoids`. These facts construct the existing
`EnumerationDriver.Ready`. No `Graph` equality or correspondence is used.

`realized` adds aligned storage and `PendingRealized` to the native flags
and selection. It derives the actual pending handle, suspended list,
decoded native value, availability and closedness. It retains the exact
classifier condition. Empty can be selected. A recursive boundary needs a
nonempty suspended bucket. Neither ordinary shape nor nonemptiness follows.

## Verification

Strict attempt 1 fails. Its complete source and raw log remain. The repair
rewrites the dependent pending-value hypotheses in the correct case and
parenthesizes the Boolean negation in the public classifier condition.
Strict attempt 2 passes with a literal empty log under Lean 4.34.1,
`warningAsError=true` and `linter.all=true`. The input premises do not change.

The installed build passes with 1310 jobs. Public readback passes and shows
all four full signatures. `offered` and `realized` use `propext` and
`Quot.sound`. `unblocked_avoids` and `ready` also use `Classical.choice`.
The aggregate Audit passes with 3733 jobs and 76525 theorem dependency
checks. The older unused `inputs` warning is unchanged. Read-only review
checks the final source SHA and each result against its stated premises.
No passing check is repeated.

All heavy work runs serially through `heavy-management/bin/capped`, with
4 GiB for Lean and focused probes, 8 GiB for the golden suite, and no swap.
Raw logs and cap receipts remain in the restart evidence directory.

## Upstream integration

Main `9d4e4d584aa7a681f075790e98466afe7531838a` is merged at
`eb52d43780d5b1f3b260bb51fbef86526d0e0830`.
Backup ref: `refs/backup/formalize-before-main-20261025-1839`.
The merge changes six Specftacular source and document files. It changes
no existing Lean proof or native CFTA enumerator source.

Existing goldens pass at one and two runtime capabilities. All six golden
signatures run in checked and unchecked modes. A public mini-list probe
compares the full four-law sequence with defaults and with
`searchParallelTests = Just 0`, `searchSpeculation = 2`, at two capabilities.
The sequences are equal. Public completion exponents -1 and 63 are rejected.
Fourmolu checks all three changed Haskell files. Cabal-gild checks the
unchanged package file. No production Haskell repair or new test suite is
added. No performance matrix is run.

The first golden invocation cannot connect to the systemd user bus.
The next invocation reaches Nix but cannot link host GMP with the Nix
linker. Supplying the user bus environment and the previously used host
compiler PATH inside Nix resolves these environment issues. The first
public probe omits the required generator argument and fails to compile.
Its input and raw log remain. The corrected input supplies `const Nothing`.
These failures are not product regressions.

An exact copy of `decideInParallel` confirms that discarded suffix work
can raise an exception or block the useful prefix. The probe preserves the
helper bytes from the imported source. This is a helper-level result.
No valid-term completion failure is established. `FINDINGS.md` records the
repair direction and two further unvalidated worker-liveness concerns.

## Strongest system claim

H6 remains `SourceCurrentColdFiniteWarmCalls.constructed_node_calls`.
Covered closed construction and a valid initial constraint cache with its
original allocation history derive the built heap. For any prescribed
finite call budget and number of rounds, the theorem derives sufficient
finite fuels and one mathematical width. The resulting modeled node-call
trace completes. Its final value is available and has exactly the original
finite-tree language, for every ambient guard and finite term under the
formal formula and entailment semantics. The inherited payload is empty.
This is not an arbitrary fixed-machine resource bound or a convergence
claim. The Specftacular completion fuel is a separate implementation limit.

## Next proof target

The selected input now has the actual root and `Avoids` precondition.
Transport this protection through native child expansion and finalization.
The cached child dispatcher currently leaves terminal child fallback open.
Use the cached terminal adapter there while preserving the outer held root.
Keep the original raw finalization target distinct from the terminal winner.

The source write-site audit suggests that stored pending buckets contain
no terminal trie. Allocation uses empty buckets. Shallow preparation stores
a bucket only after the nonterminal test. Terminal handling passes only its
descendant partition to the incoming write. Assimilation concatenates
stored buckets. Narrowing retains them. Repeated recursion clears them.
Finalization writes an enumerated value. Descent can expose terminal tries;
those transient lists take the terminal child fallback.

Relevant native sites in `cfta/src/Data/CFTA/Enumeration.hs`: allocation
300 and 394; raw mutations 397 and 453; pending intersection 204 to 210;
assimilation 502 to 507; incoming merge 521 to 523; terminal partition 718;
sole incoming caller 746; shallow storage 796 to 799; fallback 801; captured
finalization 901; narrowing 989; repeated recursion 1003 and 1536.
This audit is a proposed history invariant, not a completed global proof.

Reuse `descend_avoids`, `fresh_avoids`, `representative_avoids`,
`union_protected_class`, `union_avoids`, `assimilation_frame` and
`mergeNode_frame` from `EnumerationCorrectness`. Existing `Protected`
composition, allocation and suspension facts are graph-free.
`EnumerationDriver.enumeration_protected` remains a proof pattern because
its traversal uses `Graph`. Do not use it as native correspondence.

`Finalize.complete` already gives exact raw installation and correct
storage, waiting counts, flags and realization. Final `Safe` needs `Safe`
and rootness of the captured target at the actual pre-finalization state.
Rootness at entry alone does not establish this fact. The existing
`setValue_safe` and `ancestry_safe` facts show the final local proof step.

An artificial state with stored terminal references can merge away its
captured slot and then install there. It is not a reachable bug witness:
canonical waiting blocks its native selection, and its stored terminal
bucket conflicts with the audited native history. Do not describe it as a
native counterexample without a reachable construction.

Arbitrary mixed calls, initial-only numeric admission, selector/partition
representation, full typing/pruning, concrete solver, extraction, physical
maps and machine integers, resource bounds, convergence and the full driver
remain open. Older construction and equality targets remain preserved.
All previous evidence, including the full cached-terminal publication
summary and its custody inputs, remains unchanged at the earlier checkpoint.
