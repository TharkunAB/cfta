# Independent outer guard-heap review

Read-only source review. No build or source change was made for this review.
Reviewed draft: `/tmp/SourceCurrentOuterGuardHeapReturns.lean`, 354 lines.
SHA-256: `49ba32d0de9d6cb45490bbf858960b7bf3f1596f2bf03bdb2cb994e230184f48`.
The root agent owns its strict and canonical checks. This review does not replace them.

## Result

No material proof or domain issue was found in the reviewed draft.
The exported invariant is the causal `GuardHeap annotation` body-to-ordinary-probe profile equality for installed Mu records. It does not state that every raw guard satisfies `annotation`.

## Actual return induction

The strong induction on outer fuel is well-founded. The local walk case uses smaller-fuel node calls and smaller-fuel tail walks. Children uses that walk at the current fuel. Descendants uses those children. Ordinary node bodies use smaller-fuel rows. Node call uses the already proved current-fuel body statement. Rows use actual edge returns and smaller-fuel descendant and row calls.

Intermediate physical Good, resident values, and inherited readiness come from `OuterPrefixInvariants.reached` or its actual return laws. That module has no dependency on the new guard-heap theorem. Thus these uses do not form a circular invariant argument.
The actual memo evaluate branch reads the captured owner's readiness from the current cell. It does not assume that the new query and captured request are equal. Ready hits and finish operations change no constructor heap.
The Parent branch applies its actual successful equation and derives its conditional live inputs from initial physical fields and residency.
The Mu body uses initial physical ProbeHeap and source readiness to derive the exact unchanged-caller reconstruction equation. It assumes no future successful reconstruction or guard law.
Raw edge rebuilding leaves node records unchanged. Raw ordinary-node rebuilding uses the existing no-new-Mu law.

## Actual prefix induction

`step_heap` follows the exact `Step` constructors. Immediate body, inherited-prefix, child-walk, and indexed-demand steps leave the constructor heap unchanged. Steps that skip completed earlier edge, descendant, or node calls apply the new successful-return theorems to those same equations.
`reached` inducts on the supplied finite `Reached` proof. At each step it derives current Good and Inputs from the entry facts and the earlier prefix. It does not request a future invariant callback, Trace, Ranges, Cap, or desired result law.
`busy` derives its own exact node-dispatch prefix from the literal busy failure, then applies `reached`. It does not assume a caller-supplied busy prefix or prove that a collision is impossible.

## Scope and remaining boundaries

Initial outer Good includes checked physical Good, physical Merge storage, ProbeHeap, and ready/resident captured cells. These are substantial entry invariants. The theorem does not derive them from an arbitrary state.
Successful-return results require the actual `.done` equation. The prefix result requires the actual finite Step/Reached relation. The busy result covers the specified node-memo busy fault. The draft does not prove all failed stopping outcomes, all host execution behavior, recursive completion, a fresh-call bound, exact guard occurrence lineage, or retained-used-Mu value congruence.
No whole-forest closedness, finite input Cap, semantic outer memo result law, or future preservation oracle was found in the public premises.

## Reviewed pins

- `draft`: `49ba32d0de9d6cb45490bbf858960b7bf3f1596f2bf03bdb2cb994e230184f48`.
- `SourceCurrentOuterPrefixInvariants`: `138c3f0e8cdff1aec2b94349bbd73ccb8f3b76308acd04bf18c1b698dbecbb43`.
- `SourceCurrentOuterExecutionAncestry`: `32ec52112a2159e98d64670c35de7f6d93bb3e165cf10ee92c5393626f833234`.
- `SourceCurrentMuReconstructionEffects`: `a5840719c1c0f730dce062f4356c1c8bca2095ee030db038990634031b0c7d17`.
- `SourceCurrentParentGuardHeapReturns`: `22a28555fd934f63dc8ce66c2c22ade3d5da4450e37154ddb59ed87b15fb668a`.
- `SourceCurrentLowerGuardHeapReturns`: `92c6ae319e1c8ee96c2fa9828e1164ac7d19afd68d484449ae9f0ac2c4a5b6b7`.

The previously frozen lower manifest and its evidence were not changed.
