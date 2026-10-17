# Primary origin integration review

Recorded: 2026-10-17T17:38:05.109929+02:00

The two tests have no input premises. They construct the source heap with
FreshOrdinaryConstruction.build. The source contains a constrained finite
B = pair(leaf, leaf) with the own class [0] = [1]. It also contains the
productive plain raw Mu x.(leaf | pair(x,x)). The tested forest adds an
unselected unresolved depth reference.

selected_finite_and_recursive computes a false primary class trace for
paths [0,0], [0,1], and [1,0] at gate fuel 8. It calls PrimaryOrigins.complete
with semantic, cost, guard, union-normal, and availability facts derived
from the actual source construction. A separate initial Required completion
on the productive Mu and the computed fixed B traversal construct the
ordered child graph. Stable execution uniqueness aligns its entire result
list and heap with the new producer. The result keeps B and the unselected
reference. All returned values have ordered Origin certificates.

The retained B row has a nonempty physical own constraint. This explicit
positive witness prevents a vacuous row-origin check. Origin.physical_positive
then supplies an original row and its RowOrigin relation. The theorem also
constructs an actual initial Head for the productive Mu. It does not assert
an isolated host execution event or whole outer-worker completion.

constructed_empty_open calls PrimaryOrigins.constructed on the same actual
source. It selects no paths in a forest containing the unresolved depth
reference and the productive Mu. The result has ordered Origin certificates.
The exact original list and heap return for all worker and reader fuels,
including zero. Stable uniqueness aligns this identity with the producer.

The private instance equality uses proof irrelevance for DecidableEq. It
aligns the fixed local instance in the imported producer with the executable
fixture instance. It adds no heap or output premise. The local arrayNormalize
rule is the proved observed_eq theorem at 16. It does not replace an axiom.

Validation: primary-origin-kernels-5 has two complete signature/axiom pairs.
Both use only propext, Classical.choice, and Quot.sound. It has no diagnostic,
printer omission, or sorryAx. primary-origin-kernel-strict-1 executes the same
proof declarations without printers. Its log is empty and its exit code is 0.
All four failed attempts remain in this package. Their diagnostic output is
historical and is not counted as successful validation. No production file
was changed by this integration task.

Scope: these tests instantiate the initial primary-origin producers. The
nonempty result uses the existing qualitative StableRun completion. They do
not give a new computed fuel bound, initial outer completion, or general
node-owner progress theorem. The empty case has its stated exact all-fuel law.
