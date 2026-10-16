# Independent review of checked shared edit completion

Date: 2026-10-16 09:25 CEST.

Reviewed sources:

- `SourceCurrentAllocatedSharedEditComplete.lean`, SHA256
  `15ab3eea428bff130feb6152d35b7ac55c61034a1c361e891a247cc0dcc03c88`.
- `SourceCurrentAllocatedSharedEditRanges.lean`, SHA256
  `a51c90377cf73812ef1db46522268f75f1c7c6a004fd919c67afa0958fd36bdd`.

No material proof or model defect found in this bounded review.

`node_complete`, `children_complete`, and `list_complete` construct actual
edit graphs and their ordered annotated reads. Their public inputs contain
no completed target, leaf, edit, or future returned inventory. `known` and
`domains` concern the original captured forest. The required class coherence
and nontriviality stay explicit. The initial global tables must be valid.

The range graph contains actual leaf word-range plans. At selected positions
and later rows, its continuation checks quantify over an actual completed
prefix. The completion proof constructs that prefix first, applies its
physical effects, and invokes the continuation at its literal returned state.
The range plan supplies checks, not a successful callback or semantic result.
It remains an explicit structured operational range assumption.

Recursive heads use closedness derived from `Safe` plus an actual recursive
input and a retained leaf. Physical head completion supplies an actual
`Head`. `head_memos` derives its global reads. `head_physical` supplies the
same returned checked state and its fields. The constructed `headGlobal`
uses these actual effects and the derived final memo validity. It is not a
supplied future effect premise at the public completion endpoint.

Ordinary construction and row reconstruction use `advanceHeap`. This
advances the constructor heap while retaining the literal equality operation
state, native tables, domain cache, target slots, and merge table. Later
checks use that returned state. Raw edge reconstruction uses the original
symbol and full original guard. Its field availability follows from the
initial resident edge and actual equality-cache growth.

Unselected children remain unchanged. No whole-forest closedness premise is
introduced. Constructor-only head/row primitives remain their existing
operational model; this review does not establish GHC field forcing,
container ordering, selection CAF effects, or a literal executable worker
bound for the new edit graph. Those boundaries remain separate from finite
relational completion and independent language preservation.
