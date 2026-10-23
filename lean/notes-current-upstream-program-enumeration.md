# Main refresh: partial program enumeration and term orders

Updated: 2026-10-24. Imported main: `6b62b4afefca80bb05f5a37546212a99980aa3df`.
Merge: `78904be72914616af4bf41046ab27f65a60c6142`.
Local negative-depth repair: `058b11fe8f3706460156d7a1fc454063406a4634`.
Previous pushed formalization: `d501c53489b4ba9a41fd178c7ccdd0bf530dcde7`.

The refresh imports all 34 changed upstream paths. Each path matched upstream
at the merge. All 125970 unaffected files from the 125997-file baseline
retained their bytes and modes. All existing Lean sources, evidence, marked
drafts, counterexamples and the local equality-reduction implementation remain.
The backup ref is `codex/backup-main-refresh-20261024-0033`.
The earlier scan proof and its evidence remain sealed and unchanged.

## Behavior and formal coverage

| Area | Current behavior | Required correspondence work |
| --- | --- | --- |
| Partial enumeration | `termsPruneUntil` tests every remaining expandable UVar before expansion. It can narrow a node and defer children through shallow expansion. | Model stop, narrowing, shallow expansion, suspended constraints and partial rendering. Include blocked entries in the stop test. |
| Complete enumeration | The old driver delegates to the shared driver with no stop rule and identity narrowing. An empty node now fails before the pre-expansion oracle. | Prove a complete-result bridge and update the literal callback equation. Preserve the earlier eager-driver theorems. |
| Template refinement | Each exclusion closure shares a memo table for node and template-part lists. | Prove memo transparency and catalog-key isolation. Do not assume one global catalog. |
| Phase 4 | Program enumeration leaves unneeded type positions open. `PartialTyping` propagates unification. The caller types each program again. | Prove typing and narrowing preserve every desired program. Connect role tracking and pending checks to the actual enumeration state. |
| Compiled pruning | Finite program DAGs receive template exclusion. Unsupported shapes retain the original graph and oracle checks. | Prove finite-term exclusion and fallback. Keep terms, run multiplicities and recursive cutoff streams separate. |
| Type alternatives | Unconstrained alternatives merge before and after pruning. | Prove the specific encoding retains required correlations. A generic union law is insufficient. |
| Rewriting | KBO remains the default. Optional LPO uses an uncurried path order. | Establish the actual order laws, context compatibility, typed rewriting and termination. Two LPO defects remain open below. |
| Validation and runtime | Finite test schedules, optional rechecks, native type checks and GHC specialization select candidate equations. | These are not universal proofs of equations. Runtime casts require the documented parametric-carrier contract. |
| Parallel execution | Bucket merging and background enumeration share work. Limits can retain fewer completion rules. | Prove merge behavior and cancellation cleanup. Process-wide heap samples are not per-task memory bounds. |

A partial result need not have any accepted completion. The native core probe
returns a root hole for `EmptyNode` when the stop rule always accepts.
This is the documented API behavior. Do not apply complete-term acceptance
theorems to these partial results without an additional completion argument.

## Haskell repairs for external work

The negative-depth defect is fixed locally in `058b11fe8f`.
Before the fix, `mtauWithin (Just (-1)) []` did not return before the
200 ms probe timeout. The parser accepted the same invalid bound.
The fix rejects it in `parseOptions`, the shared `searchPhases` entry,
and the exported `mtauWithin` constructor. Zero and positive bounds retain
their previous behavior. An external agent can import this commit into main.

Two optional LPO defects remain open in `Specftacular.Rewriting.lpoCompare`.
Both native probes use the public type validator and well-typed terms.

1. With `PathOrder ["e", "c", "f"]`, let
   `s = f ([] :: [A]) (c :: Bool)`,
   `t = f ([] :: [B]) (d :: Char)`, and
   `u = f ([] :: [A]) (e :: Int)`.
   The signature has parametric `f :: A -> B -> Int` and `f` returns zero.
   The actual comparisons are `s < t`, `t < u`, and `u < s`.
   The cycle remains after `canonicalTypes`.
   Full annotation equality and the raw fallback cause the inconsistency.
2. With `PathOrder ["f", "a"]`, use `f = id`, `a = id`, and `x = A 0`,
   with `f :: (A -> A) -> A -> A` and `a :: A -> A`.
   The actual comparator has `f a > a`, but `(f a) x < a x`.
   The rewrite function descends into function positions. Local decrease
   therefore does not establish decrease of the enclosing application.

Comparing erased programs and using a consistent annotation tie-break can
address the first defect. It leaves the second defect. A complete repair must
establish an order compatible with the actual applicative contexts or change
the rewrite strategy and corresponding pruning rules. No LPO patch is applied
in this checkpoint. No rewrite-loop execution is claimed.

The source reviews also identify static cancellation-cleanup concerns and a
README schedule undercount. These are separate from the confirmed defects.
The default schedule has 1000 random cases and 64 additional cases.
The README describes only 40 additional cases. No documentation repair is
included in the imported Haskell fix.

## Verification and retained work

The existing CFTA suite passed: 325 examples, zero failures.
The complete Specftacular golden suite passed in checked and unchecked modes.
All golden cases use phase 1. They do not establish phase-4 correctness.
Both Specftacular libraries built with strict GHC warnings after the repair.
The small phase-4 probe used depth 1 and four additional rechecks. It returned
identical laws in serial, parallel and enumeration-ahead modes with two RTS
capabilities. This is evidence for that signature only.
The three negative-depth entry probes and the depth-zero probes passed.
All nine core partial-enumeration and exclusion-catalog probes passed.
Fourmolu checked 23 imported Haskell paths. Cabal-gild checked both changed
Cabal files. No new package test is committed.

The first suite attempt failed to link `libgmp` in the Nix environment.
The documented host compiler PATH fixed that environment failure.
The retained probe attempts also include harness-only failures for a missing
OverloadedStrings flag, direct CFTA package exposure and strict warnings in
temporary probe source. Corrected probes retain the original sources and logs.
These are separate from the confirmed runtime defects.
Host linker metadata warnings remain in the library build log.

Evidence is in `lean/restart-evidence/20261024-main-refresh`.
It retains the baseline, source reviews, actual probe sources and logs,
the earlier scan publication receipts and the queued counter-consumer proposal.
The earlier proposal is not a new proved or compiled module.

H6 `SourceCurrentColdFiniteWarmCalls.constructed_node_calls` remains the
strongest combined execution and finite-tree language theorem, under its
existing premises and formal guard interpretation. No new Lean proof or Audit
run is claimed by this refresh. Existing source bytes are unchanged.
Next, model the shared enumeration driver and prove the no-stop bridge,
with the partial-result contract stated separately. Retain the queued H23
scan-chain/rebuild counter proof as the next independent counter target.
Full-pipeline composition, upper resources, practical width, Haskell/solver
correspondence and convergence remain open. The full goal remains active.
This record precedes publication of the refresh evidence and its push.
