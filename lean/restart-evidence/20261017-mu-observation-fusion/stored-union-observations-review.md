# Actual stored union observations

The module supplies three public theorems. `closed` proves the exact repaired
stored return for a closed value at any heap. `members` constructs an ordered
sequence of actual stored member calls from initial `Ready`, available source
members, and available replacements. It retains `Keeps` and all output
availability. It accepts arbitrary nested Mu members.

`complete` constructs the actual repaired stored union return and the actual
ordered calls for its original members. It retains the root and member cache
effects, output availability, and growth from the member heap to the root heap.
For every finite depth and every fixed view, the returned root has the same
open observations as the member-result list.

The theorem covers open and closed roots. For an open root, the existing
encoded execution supplies its actual member calls and constructor request.
A separately constructed member sequence has identical outputs and final heap
by determinism of the actual calls. This derives the intermediate ready heap.
Actual union normalization then supplies both reference and row observations.
For a closed root, source coherence and the resident union free-name equation
prove that every original member is closed. The member calls retain their
original values and heap. The literal union observation theorem supplies the
result. No additional closure or union-normality premise is imposed.

This theorem compares a stored union reconstruction with the calls of its
own original members. It does not compare reconstruction after an earlier
makeUnion with reconstruction before that normalization. It does not claim
physical fusion, cross-view transport, nested Mu observation fusion, or outer
convergence. No desired member result relation or future completion is a
caller premise.

The final strict source is `stored-union-observations-direct-2.source.lean`.
Its log is empty. The canonical build passes 570 jobs. The public group checks
all three declarations. Kernel attempt 1 checks two no-premise constructed
cases. Actual source construction produces an open union with a productive
raw Mu, a bare reference, and an ordinary member. It also produces a closed
union with the same Mu and ordinary member. Both cases derive initial `Ready`,
source availability, and replacement availability. They retain the exact
three-member and two-member output lengths. The closed case also checks its
literal same-heap return.

All selected runs use Lean 4.34.1. Effective cgroup readbacks record 4 GiB
memory max, 4 GiB memory high, and zero swap. All eight explicit printer
settings are present in the public and integration probes. All selected
axioms are standard. Source attempt 1 and its raw log are retained. It had one
local proof variable name error. No old source or frozen evidence changed.
