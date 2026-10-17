# Recursive selected-path positional closure

Reviewed 2026-10-17 02:06 CEST. No Haskell run or repair occurs here. The new
Paths module is a pure initial mask foundation. It does not prove general
selected completion or preservation through a complete class edit.

## Actual branch and state contracts

- `SourceCurrentAllocatedPartialWorker.lean:74–95` returns Empty and explicit
  union directly, rebuilds Mu, rejects a bare reference, and traverses ordinary
  rows. These outer terminal branches do not settle selected paths below Mu.
- The same worker at `119–147` calls the parent on each ORIGINAL row, descends
  through that RETURNED edge, then visits the ORIGINAL suffix. The inherited
  prefix reads the returned raw guard, combines inherited first, retains its
  actual equality-operation return, and runs once before indexed children.
  Lines `150–170` erase on contradiction or descend at the actual child index.
- `SourceEqualityRequiredGraph.lean:28–66` has the lower `RequireChildren.selected`
  constructor at `49–52`. An empty Needed returns before node inspection.
  Nonempty Mu/union reads the actual Head. Ordinary rows reject missing arity
  before recursion and retain the original complete raw guard when rebuilt.
- `SourceCurrentAllocatedSharedEditGraph.lean:32–70` invokes Leaf before node
  inspection. Selected children use actual signed map lookup and thread the
  reached warm state. EditBelow Mu/union uses the actual Head; ordinary rows
  retain the original full guard. EditList ignores a root leaf at `73–80`.
- `SourceEqualityProjectionGraph.lean:18–54` uses signed lookup. Each ordinary
  step projects every existing selected row child, then performs the actual
  source Union. Recursive Head keeps the SAME remaining path. Forest root is
  a separate Union branch. A missing forest index returns Empty.
- `SourceCurrentSelectedClassRecords.lean:46–102,105–117` retains exact original
  record positions. Its receipt implies an ordered sublist and equality of
  the retained record paths with the selected paths. It is not an endpoint
  annotation or completion theorem. `SourceCurrentAllocatedRecordScanWorkerActual`
  supplies exact literal/graph endpoints at `108,132,157`; it retains reached
  checks and does not establish this new recursive structural invariant.

The Haskell source agrees with these boundaries. `Equality/Operations.hs:207–244`
partitions original own classes, checks refused classes before Require, requires
selected paths, and reduces classes with a right fold. Each class captures its
incoming forest. Its callbacks project the OTHER captured paths, merge each
projection, and intersect them with the literal seed rotation. They do not
project earlier callback outputs. `Interned/Operations.hs:787–792,813–814` gives
the separate value-root and forest-root projection rules.

Raw entry and internal recursive exposure must remain distinct.
`Equality/Operations.hs:260–270` refuses bare Rec and raw InternedUnion before
metadata tests. A closed unconstrained Mu passes without inspecting the rest
of the path. Its later selected projection can enter its body, unions and
bound references through actual substitution and Head. A nonempty direct path
at an unresolved Rec is an error (`Interned/Operations.hs:792`). No new theorem
here turns that error into success. Annotated reference syntax alone is not
closedness or a binding certificate.

## Initial invariant and proved mask laws

Use existing `Annotated P` with `P guard := SourceMemoGate.plain guard = true`.
The plain test includes empty effective equalities AND supported residual
syntax. `SourceCurrentHereditaryUnconstrained.lean:104–124` proves the exact
physical empty own payload and actual unconstrained read. It does not replace
P with a test of the stored equality field alone.

Root's `SourceCurrentConstrainedCap.lean:18–27` permits hereditary recursive
values at any finite depth, consumes depth only at ordinary layers, and keeps
depth through stored union alternatives. At zero it is exactly Annotated
(`38–40`). This predicate bounds nonplain ordinary positions. It does not
identify safe selected endpoints.

New `SourceCurrentConstrainedCapPaths.Supported P path value` (`25–34`) is an
INITIAL syntactic mask. A hereditary value accepts every remaining path. A
nonempty ordinary branch checks every actually selected row child. A union
checks every stored alternative at the same path. A nonplain Mu has no mask
constructor. At an empty path the mask is exactly Annotated (`37–48`). Missing
positions impose no endpoint condition. No future result, completed query,
WordRanges or enclosing completion occurs in this definition.

The module proves:

- Signed selected-child and union-member projections (`51–67`).
- Mu boundary iff Annotated, predicate weakening, and safe suffix extension
  (`70–96`). Suffix extension is useful for congruence path extension; it is
  not a bound on inherited normalization depth.
- `of_cap bounded path long` (`99–111`): Cap P d v and d ≤ path.length derive
  Supported P path v. This is a simple initial sufficient condition. A shorter
  path can also satisfy the mask when its selected branch enters a hereditary
  hole early. Unselected branches need not have a smaller cap.
- The forest's first index is separate (`114–149`): if every captured value has
  Cap P d and the remaining tail has length at least d, that forest path is
  supported. A whole forest-root path requires every captured value annotated.
- `operand_paths` (`152–158`) transfers masks for the ORIGINAL class paths to
  the exact ordered `SourceEqualityClassTarget.operandPaths`, including its
  natural-to-signed conversion and selected-path filter. It assumes no runtime
  choice, uniqueness of path lists, or future target annotation.
- Nonempty bare-reference Project is impossible (`161–166`). Actual zero-tail
  ProjectRows returns annotated selected endpoints (`169–185`). This is the
  only new actual projection preservation endpoint in this module.

A useful initial selected domain is therefore: a finite cap with closed,
available hereditary plain holes; actual effective own class paths have
ForestSupported on their original captured children. Requiring this for ALL
own paths is an initial sufficient condition. Requiring it only for an exact
retained selected sublist is weaker, but must use the actual initial scan
receipt. Neither version can replace the later preservation proof.

## Failed candidates and scope

The checked kernel `short_endpoint_counterexample` constructs a depth-one cap
with a non-P nullary root row. Its actual `Project []` graph returns that SAME
nonhereditary value. Thus Cap alone does not make short endpoints plain. This
is a pure model counterexample to that proposed invariant. It is not a new
Haskell defect, a closed physical-cache counterexample, or a divergence claim.
Haskell `Equality/Operations.hs:129–138` explicitly leaves the mixed case open:
unequal path lengths can move a constrained node into a plain unfolding.

Existing executable evidence remains relevant. The frozen
`20261017-recursive-source-progress/recursive-haskell-boundary-review.md:79–94`
records a genuine selected recursive run with ordinary height 1 → 4, and a
native intersection whose result exceeds the minimum ordinary input height.
It also records fixed own path depth 4 with inherited payload depths
0,3,4,5,6,7,8,9 under repeated combine/descend. Those results refute direct
extension of the finite-ordinary height rank and a fixed own-depth payload
carrier. They do not prove general divergence. No test was rerun here.

## Concrete remaining theorem chain

1. Prove actual Head/Union preserve the path-sensitive mask, or use the stronger
   initial depth/length condition with an actual cap-depth projection theorem.
   Root owns the separate supplied-graph CapProjection proof. Its completed
   graph input does not by itself prove that all selected executions exist.
2. Prove actual Require retains BOTH cap depth and outstanding path masks.
   Length preservation alone is insufficient. Retain exact signed positions,
   row filtering, actual constructor readback, and MuStored on every prefix.
3. Prove class targets/callbacks produce Annotated plain values from those
   INITIAL endpoint masks, existing actual local Required/Merge/native laws,
   physical closedness and causal stores. Native input words/capacity remain
   separate numeric obligations. Then prove actual edit reconstruction retains
   the cap and the masks of every still-pending class. A right fold must thread
   that law at its literal tail return. Do not assume the new output mask.
4. Derive returned-edge cap/position certificates from actual cold parents,
   including rejected/erased/sentinel branches. Install them at the exact
   captured outer owner before warm reuse. Semantic EdgeLaw alone cannot
   identify returned children. Current conditional plain-own stored Shape is
   useful for the depth-zero suffix; mixed constrained ancestors must remain
   permitted.
5. Use a rank tied to constrained depth and actual current records, with a
   depth-zero structural/ordinary suffix rank. Original ordinary height alone
   fails. `PartialActiveOrder.lean:30–59` gives the original ordinary phase
   inequalities; `64–85` ties coherent physical keys to exact stored ranks.
   The recursive extension must retain that owner alias transport, exclude
   equal active owners, and restore sibling bounds through reverse active
   frames. It cannot require recursive Idle while an ancestor is evaluating.

The existing `PartialPlainNode.finite` (`117–138`) is a useful suffix theorem,
not a transfer for mixed constrained caps. PlainRegion permits opaque Mu and
union terminals and is weaker than hereditary annotation. General arbitrary
constrained recursive selected progress, repeated-pass convergence, dynamic
resource bounds, and whole-library Haskell correspondence remain open.
