# Executable outer narrowing and enumeration actions

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `b2fe79af95c4c589b17cd813c801ab159dad63b6`.

## Executable stage

The prepare definition computes the existing outer narrowing once. Its input
contains the original selected raw UVar, complete old Value, old handle,
original suspended list, incoming metadata and native heap. Native narrowing
and representative lookup have separate fuel arguments. No first pending
read is repeated inside this suffix.

The existing native Result retains the actual heap on success and failure.
Its successful payload retains the actual narrowed Value beside an optional
existing enumeration Unit action. No new state or result carrier is added.
The retained Value supplies the later native Right input without narrowing
again. The action can retain its computed handle without a new output field.

A native failure retains its exact fault and heap. A completed Empty result
selects the actual reject action before encoding or identity comparison.
A nonempty result with no encoding retains its Value and heap with no action.
It is not Empty rejection or a native fault. An encoded nonempty result
selects pure Unit for equal handles. Changed handles select the existing
representative lookup followed by the write at its returned root, using
the original suspended list. An error of that action remains an enumeration
error. Rejection remains the empty list. Neither exposes a final enumeration
state or removes the native heap already returned by prepare.

## Actual pending-slot connection

The completion theorem starts with Ready native heap, all-slot realization,
Total representatives, the actual first pending getValue success and a full
frame into the actual entry state E. The same read derives the complete old
Value, lookup, encoding, availability and closedness. The theorem invokes
the existing outer pending consumer once and keeps its actual chosen native
run, heap H', Keeps, both complete readbacks and larger-native-fuel equation.
It assumes no desired output or graph equality.

Each result branch includes the actual prepare equation for its literal
returned action. Empty and equal handles allow every representative fuel.
Equal surviving handles retain full Value equality and pure success at E.
Equal handles do not imply that native narrowing kept the initial heap.

Changed surviving handles retain the same chosen representative fuel, root,
size, compressed Q and final F from the consumer. The prepare equation and
actual representative-bind-write success use those same witnesses. The
old slot, original suspended list, slot bound, full E-to-Q and initial-to-Q
frames, exact final record and new slot remain. All-slot realization holds
at E, Q and F in the actual returned native heap. No full frame crosses the
changed values write. Membership and holeKey retain the original raw UVar.

## Validation and retained work

The first strict input fails because the changed prepare equation does not specify EnumGuard and six body uses select deprecated aliases. A separate reviewed V2 adds the explicit EnumGuard argument. The body uses the supported ite_eq_left and ite_eq_right lemmas. The executable definition is unchanged. The second strict input passes with a literal empty log. Both inputs and the actual failed output remain. The public readback retains all 152 lines with both complete signatures and no display omission.
The installed build passes 576 jobs. Audit passes 3688 jobs and
76131 dependency checks, with one older replay warning and no new
source warning. Both complete public signatures and actual axiom reports
were read. Both declarations report exactly propext, Classical.choice and Quot.sound.
One public definition, one theorem and one named local Monad List instance
are added. No helper, packet type, global instance or proof limit is added.
All exact frozen declarations, scoped binders, source cuts, independent
reviews, raw attempts and resource receipts remain. The baseline has 130062
tracked files. The preceding outer pending checkpoint's post-seal inputs
remain. The original source-plan payload hold and its separate reviewed
addendum remain. This was a prospective interface correction, not a failed
compiler attempt. The actual declaration and body history is recorded with
the current checkpoint evidence.

## Remaining scope

This stage computes the outer result and its actual enumeration suffix.
It does not change the pure Nat narrowing interface in EnumerationUntil.
That interface still needs its native heap, Value and Graph connection.
The older Nat Oracle also needs genuine Value/Graph correspondence before
it can consume the retained native result. A callback equality cannot
replace either connection.

Native NodeId extraction, graph classification, expandable and canonical
waiting indices, memo2, effectful intersection and assimilation remain open.
Concrete typing, unification, hole keys and fits/admits laws remain open.
Right/Left sequencing, expansion, repeated recursion, whole scheduling,
typedTypes and lazy emptyAt demand, semantic pruning, global canonicality
and mutation histories remain open. Phase4, resources, practical machine
width, extraction, runtime/solver correspondence and convergence remain.

H6 constructed_node_calls stays strongest combined with its covered closed
construction, valid initial cache, original allocations, finite rounds and
empty inherited-payload language condition. H23 and older constructor and
equality work remain queued. The full goal stays ACTIVE and incomplete.
No Haskell source changes. FINDINGS retains all six imported repair handoffs
first. All earlier proofs, counterexamples, repairs, marked drafts and the
optimized interned core remain. This note precedes evidence and push.
