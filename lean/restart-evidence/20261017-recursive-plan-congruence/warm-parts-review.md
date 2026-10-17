# Warm construction parts

The source supplies seven public theorems. Each theorem decomposes an actual
successful warm construction at one common heap. The generic `bind` theorem
uses prefix replay to identify its intermediate heap. It does not require
antisymmetry of `Grows`.

`many` retains the ordered child calls. `rows` retains the ordered literal row
plans. `node` and `union` retain their actual list result and final constructor
work. `callback` retains its raw body call and exact filter. `binder` retains
both normalized probes, both raw body calls, both filters, and the final
request. Every retained call starts and ends at the same common heap.

The specialized theorems require only cache validity and the actual warm parent
return. They accept arbitrary nested binders and union members. They do not
require `Ready`, availability, closure, a semantic result relation, or a future
callback result. They verify a warm observation. They do not construct a first
execution or prove recursive plan congruence by themselves.

The final strict source is `warm-parts-direct-3.source.lean`. Its log is empty.
The canonical target passes 155 jobs. The imported public group checks seven
signatures, full proofs, and axiom sets. The two constructed integrations have
no caller premises. The first constructs an allocating nested raw/smart
binder. The second constructs a node with an ordered union and nested binder
child. It derives the row, child-list, union, and final node work at the actual
returned heap. Both integrations derive all cache validity facts from the
actual initial execution. The second proves strict edge-counter growth.

All selected runs use Lean 4.34.1 and effective cgroup limits of 4 GiB memory,
4 GiB memory high, and zero swap. All eight proof-printer options are explicit
in the imported public and integration sources. The selected proofs use only
standard axioms. The generic `bind` theorem uses no axioms.

Attempt 1 could not connect to the user systemd bus in the restricted sandbox.
Its immutable source and raw log are retained. It did not execute Lean or read
cgroup limits. Attempt 2 executed under the cap and exposed required unfolding
of the repaired source equations. Attempt 3 resolves those elaboration errors.
No previous source or evidence file changed.
