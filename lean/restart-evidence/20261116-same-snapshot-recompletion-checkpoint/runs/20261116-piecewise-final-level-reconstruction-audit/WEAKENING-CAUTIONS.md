# Failures of weaker claims

These are mathematical examples for the design. They are not accepted-source
traces, runtime counterexamples, or Haskell bug claims.

## Held-only avoidance is insufficient

Use singleton UF classes. Initially A is an expanded closed leaf at level 0,
N is pending at level/frontier 1. Finally A remains that leaf, and N expands to
`hole A`. A final witness can assign N level 0, A level 1, frontier 2.
Protection of A holds. A different held class is avoided. The proposed piecewise
levels retain A at 0 and assign N at least F0=1, so the N-to-A inequality fails.
No Nat level below the preserved A level 0 can repair it. Strong birth correctly
rejects this new-to-old dependency.

## Value retention alone does not preserve raw aliases

Initially A is expanded at level 0, X is pending at frontier 1, in distinct
classes. If a later forest aliases eliminated X to root A, the stored A value
can remain unchanged in a Safe final state. The piecewise old branch would use
L0 A=0 and L0 X=1 inside ONE final class. Full Protected.classes forbids this
merge. A value-only preservation claim does not suffice.

A hole ID different from A may still be an eliminated alias of A. Avoidance must
exclude SameClass, not just raw ID equality.

## Arbitrary raw monotonicity is false

Take an initial singleton pending root with frontier 0 and no expanded slots.
Give a distinct, unallocated default singleton ID h initial level 100. Give all
final IDs level 0 and final frontier 0 in the unchanged state. Both orders and
all protection/birth requirements hold. The construction assigns h level 0.
Thus `forall uv, L0 uv <= Lnew uv` is false. Initial Safe plus `uv < counter`
is the required restriction for the allocated bound.

## Arbitrary target lower bounds are false

If an alleged raw target is an original expanded class at level 0 with F0=1,
its level must remain below F0. A target-above-cut assertion therefore needs
InputsPending or equivalent actual class separation. It cannot follow just
from calling some list a removed bucket.

## Do not retain the old frontier

A shifted final pending slot has level F0+F1, not F0. The exact pending field
fails if the reconstructed frontier is kept at F0 when F1 is positive.
Fresh expanded levels can also be at least F0. The frontier must shift with the
new block of levels.
