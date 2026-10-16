# Next target: complete current recursive caller invariants

Read NEXT-PROMPT.md, HANDOFF.md, root FINDINGS.md, CONTEXT.md,
docs/adr/0004-explicit-graph-boundary.md, and
lean/notes-current-inherited-caller.md. The eight current modules are frozen
in frozen-modules.json. Preserve every older constructor and equality proof.
Source main is 8f85ddb6. No Haskell implementation or test changes occur.
Record each future Haskell fix first in root FINDINGS.md, with its failure
case, affected files, commit, checks, and upstream status.

## Completed current boundary

The actual reduced-edge memo wrapper is composed. Its fresh and suspended
evaluation branches derive their owner inputs, run ParentEdge.finite,
derive an independent language law, retain the exact running cell, finish
that cell, and transport the law to the requested candidate. Ready hits keep
the whole caller state and need no local range plan. finite_or_busy covers
all valid starts without turning a busy observation into a returned value.

The raw outer graph and indexed read schedule follow the actual source.
The inherited prefix runs once on the RETURNED edge. Its inherited-FIRST
combination can short circuit before the own accessor. Each child receives
its actual allocated descent at its actual index. Raw same-arity setChildren
follows those children. Ordered rows and literal modifyNode are modeled.
Those graph definitions do not yet prove the entire caller's body law.

## Required next theorems

1. Define protected evaluating cells for both current result families. Prove
   their preservation across actual completed current calls, excluding a
   successful call to the same busy handle. Reuse the pure FlatMemoThunk
   Running/Returned laws. Reprove their projection for this State. Do not
   transfer a historical one-table worker's execution theorem.
2. Preserve the explicit InternedFreshOrdinaryProbeHeap.Heap invariant through
   the current parent/local/Scan/query/head/edit/decision graphs. The new
   MuRebuild component preserves it through constructor work, optionalBinder,
   and actual checked native execution. Ready, Effects, or Keeps alone do
   not contain the filtered-probe invariant. Actual original construction
   derives it. Its whole-caller transport cannot be assumed.
3. Prove a mutual physical and language invariant for NodeCall, NodeBody,
   EdgeCall, EdgeBody, Rows, Descendants, Children, and Walk. Use their actual
   current Reads annotations and returned state. A child callback must not
   assume the desired recursive body law. Smaller actual recursive calls
   must discharge it. The shared budget is only the local checked budget;
   it is not an outer recursion bound.
4. Derive inherited-child satisfaction from the combined prefix and actual
   indexed descent. A child law preserves membership under its descended
   payload. Its parent needs that implication from the original full guard
   and inherited satisfaction. Compose the exact same-arity raw rebuild,
   returned-row order, and modifyNode receipts.
5. Add the literal bounded executable worker with complete reached state.
   Keep done, errors, incomplete fuel, busy, absent, and unexpected Rec
   distinct. Hits may succeed at zero body fuel. Prove projection to the
   completed graph and sufficient stable bounds on a justified input domain.

General constrained outer termination still needs a well-founded argument
or a verified narrower supported-domain contract that remains explicitly
separate from the full goal. Source Operations.hs:119–142 records the open
unequal-length path case. Semantic narrowing and finite local parent calls
do not imply decreasing narrowed-child depth. Public reducePartially is one
pass. Bounded repeated callers need every individual pass to complete.
Unbounded identity convergence is a different obligation.

## Source and runtime limits

Do not replace the current checked parent with the old guarded edge worker.
Do not add the old prepare interner. Physical key equality gives inherited
satisfaction equivalence; it does not require identical payload metadata.
The Mu source pattern reconstructs via createMu. It is not unconditionally
the original record; its proved cleanup can differ.

The current graphs are serial logical schedules. The GHC lazy evaluator,
IntMap/list demand, noConstraint CAF allocation, concurrent publication,
machine Int conversion for child indexes, native word capacity, and identity
lifetime retain separate representation obligations. Solver IO, randomness,
callbacks, codecs, public frontends, heterogeneous recursive generators,
and all separate Sized contracts remain in scope. The optimized interned
core remains. Do not report a whole-library proof at a component checkpoint.

Pinned full Audit is GREEN2371 with 57099 dependency checks. Final log is
full-audit-final.log. Only standard foundations and the old unused inputs
warning remain. Reuse unchanged-source strict Nix all-component build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.
Use one canonical Lake process at a time and poll its actual handle to a
terminal result. Keep evidence sources and logs; exclude compiled artifacts.
No board posts or deployments. Push verified formalize checkpoints regularly.
