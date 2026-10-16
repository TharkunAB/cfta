# Current row and descendant language composition

Source: `MicroCFTA/SourceCurrentAllocatedPartialForestLanguage.lean`.
The module adds semantic induction steps for actual current caller traces.
It does not prove the whole mutual caller invariant or general completion.

`RowsLaw` is indexed by the exact `PartialGraph.Rows` trace. Its independent
language is an existential union of the complete original edge languages.
`rows_cons` composes the first actual edge law, the descendant law for the
RETURNED narrowed edge, and the tail row law in source order. The trace
indices retain order and multiplicity. The language interpretation does
not distinguish repeated identical alternatives.

`descendants` consumes an actual `InheritedPrefix.Receipt` for the same
raw returned field, inherited value, original checked state, and combined
payload. Its child trace starts at the literal `prefixState`. The child
law describes that exact trace. A literal raw `EdgeReceipt` then retains
the full returned guard and the replacement children. Output acceptance
narrows through the child law. Input acceptance and inherited satisfaction
supply the combined payload through `Receipt.guard_satisfied`, which uses
the actual inherited-FIRST combination. No unrelated sibling is assumed
closed. No guard law is supplied as an arbitrary callback.

`ordinary` consumes the smaller actual `RowsLaw` and literal `NodeReceipt`
from modifyNode. It derives the parent `NodeLaw` from the exact original
row union and actual reconstructed row union. Its inputs contain no
parent result language law. Actual physical prefix/rebuild receipts can
be derived by the already proved constructor/prefix endpoints. The
external integration kernels explicitly derive the final raw edge and
node receipts from `edge_verified` and `modify_verified`.

The unchanged empty and union branches satisfy `NodeLaw` by reflexivity,
including inherited contradiction. Current Haskell `Equality/Operations.hs`
lines 84–86 returns EmptyNode and InternedUnion unchanged. There is no
counterexample to this law. The law does not claim that every output term
satisfies inherited constraints. It claims narrowing and exactness for
input terms that satisfy inherited constraints. The Mu branch still needs
its own reconstruction law. Recursive call laws remain explicit smaller
induction hypotheses and must be discharged by the parent mutual proof.

The module does not replace any actual trace, heap, child list, guard,
operation table, or global bundle. It does not transfer the historical
worker execution. Whole-caller termination, GHC forcing/publication,
physical table implementation, and machine identity boundaries remain.
