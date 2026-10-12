# Flat choices in mutually recursive keyed families

`KeyedNaryAlignment.lean` defines typed mutually recursive bodies with any
finite number of choice branches. Each body can use finite sources,
retained finite masses, arbitrary key occurrences, maps, pays,
applications, and user labels. Intermediate application values can have
different types. All keys share one root value type.

The value, term, and paired compilers use the same ordered alternatives.
The term compiler adds each original flat branch label before it lowers
the choice to the existing binary grouped algebra. The lowering does not
add nested binary term labels. The proofs retain the complete ordered
classes, class counts, valid and invalid decoder results, minimum tables,
size guards, and exact finite derivations. Empty and singleton raw choices
are included. A branch with no member at the current size retains its
original position when it becomes live at a later size.

`KeyedNaryMass.lean` proves the value and term projections of the paired
family. It preserves retained group mass, every rank, and each rank's
probability. Its bounded projections use the actual bounded grouped
record. A retained finite leaf can supply sparse masses through
`retainedLive`; filling an unused empty-class mass does not change the
stored class mass or a member probability.

`KeyedNarySource.lean` defines independent flat value, term, and paired
record compilers. Each choice uses `GroupedRecord.merge`. The proofs compare
all four observable fields with the binary lowering: mass, ordered decoder
members, the value sampler, and the complete ranked sampler. The proof uses
`GroupedMergeAssociativity.lean`; singleton laws require valid source
records, including coherent empty records. The full guarded family laws
then derive the simultaneous flat record equations. No source knot or
whole-family replay postcondition is assumed.

`KeyedNaryDispatch.lean` models the source `mergeRecursiveGroups` dispatch.
An empty group list returns no group. A singleton list retains the child
record and callback unchanged. A list with at least two groups uses one
flat choice in the original order. This distinction matters: raw
`choiceRecursive` adds `Choice 0` for a singleton, but the same-key merge
shortcut does not call that function. The full family theorems apply to the
recipes that this dispatcher returns. This adapter does not claim that an
empty raw choice is a successful public generator construction.

`KeyedNaryFields.lean` connects the local callback operations to independently
compiled ordered term classes. Its finite-leaf contracts are local. It
proves range, source order, and distinct positions for all candidates,
including false checked flags. It also proves inverse correctness below a
requested forest-height bound.

`KeyedNaryInverse.lean` derives each count and selector equation from the
actual keyed source program and its discovered minimum table. A simultaneous
induction over all keys proves the complete inverse. Each `AtKey` and
`Family` boundary checks the key labels and reduces the requested forest
height. The proof uses only the local finite-leaf contracts. It assumes no
global inverse equation.

`KeyedNaryCausality.lean` proves that any two sufficient fuel amounts give
the same complete candidate list. It derives the source callback equation
with no fuel parameter. It also proves exact member dispatch and rejection
of wrong keys and malformed wrappers. `KeyedNaryQuery.lean` connects these
callbacks to the public replay filter and the actual bounded grouped
decoder. It proves every per-key and global rank preimage, source order,
and distinct returned ranks.

`KeyedNaryExamples.lean` checks two mutually recursive keys. The first body
has three flat branches. Two retained leaves have masses nine and one; the
third branch is empty at size zero and becomes live later. The examples
check exact counts, the retained nine-to-one ranked probability law, all
three inverse views, wrong outer and inner keys, and original branch two.
They also distinguish empty and singleton raw choices from merge dispatch.
All examples reduce in the Lean kernel.

A separate public Haskell replay probe, run during integration, checked
eight classes of a two-key recurrence with four weighted operators, two
base leaves, and a delayed third same-key leaf. It checked 285 bounded and
unbounded inverse ranks, support acceptance, normalized key masses, and
within-key probability tables. The independent recurrence includes the
operator group's source `totalCount = 4` mass scale. This executable check
supports the source comparison; it is separate from the Lean proofs.

The size guard used for the family equations is weaker than the source's
combined size and term-growth rejection test. A user label and a plain pay
have the same value-size lowering but different term-growth behavior. An
exact term-growth comparison must use the original typed syntax; it must
not recover labels from the lowered value recipe.

Key codes must agree with source key identity. Cross-key term separation
also needs an injective code. Runtime key representations, Haskell lazy
evaluation, container behavior, arbitrary finite callback implementations,
and extraction remain correspondence boundaries. The finite-leaf contracts
state their exact obligations. Member ranks count source derivations.
Distinct returned rank numbers do not assert a quotient by equal terms.
