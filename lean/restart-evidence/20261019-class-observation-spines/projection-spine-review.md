# Actual projection and read history

The complete final source was read. It has SHA256
`b58d94bcae9b63cffd8b9193d0d795609efbf8206adfe14c62f0dbb5e1282499`.
The module has two public declarations: the `Spine` type and `project`.

`Spine` is indexed by the exact Project and Read graphs, selected row
position and complete row value. Its root case retains the actual Read.
That read can unfold Mu. It is not replaced by physical RowAt.
Its recursive case retains the exact Head and remaining body projection.

The ordinary case retains the final observed row position, canonical
result lookup, raw union row preimage, selected projected operand, and
that operand's actual ReadAll prefix, Read and suffix. It retains the
selected original row and signed child lookup in the ProjectRows graph.
The projection prefix, selected call and suffix keep their actual states.
The recursive Spine uses that same call and the selected operand Read.
Missing source children do not add projected operand positions.

The raw union row position is some equal full-row preimage. It is not
asserted to equal the selected read prefix length plus the read index.
The selected causal branch is fixed independently by the operand index,
actual operand Read and recursive Spine. No external-reader forward
growth is asserted. Callers must retain their own reader support.

The producer follows mutual Project and ProjectRows induction. Actual
successful effects derive intermediate semantic and cost heaps and
availability. The union survivor inverse uses those effects without a
closed-input premise. It does not assume a desired source relation,
ordinary-row occurrence for a Mu, path safety or a decreasing rank.

Selected strict3 has exit 0 and an empty raw log. Canonical1 returns 0.
Its only warning is the unchanged dependency warning in ClosedCompletion.
Public1 prints both full declarations with all eight required options and
standard-axiom checks. Direct1 and direct2 retain their elaboration errors.
All five runs have verified 4 GiB memory and high limits, zero swap, and
a five minute wrapper cap. The independent 13-pin review is retained.
No Haskell bytes change or defect is asserted.
