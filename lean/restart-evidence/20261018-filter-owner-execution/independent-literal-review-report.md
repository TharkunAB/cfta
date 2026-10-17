# Independent review of literal reconstruction congruence

Reviewed on 2026-10-18 at 01:09 CEST. No material issue found.
This review is read-only. It adds no proof declarations or proof pairs.
It repeats no Lean build or probe.

## Frozen production

- `SourceCurrentStoredLiteralCongruence`:
  `619b38bd7a7668ee2ee332f5d6c81f36cee65e66c4ee03c15c16864c1688251c`.
- `SourceCurrentLiteralPartsObservations`:
  `b31c39d7c3670ac65f34b25f7487367d793287c9d06f1cfc1a0f2fcb00004fc4`.

The selected numbered strict snapshots have those exact hashes.

## Reconstruction contract and repaired executor

The namespace opens `InternedFreshOrdinaryStoredSubstitution.execute`.
This is the repaired stored executor. Its plan uses the repaired fresh
construction and its actual warm replay theorem. No old shallow executor
or binder-free restriction enters the new public statements.

The private `atom_parts` case treats each complete reference or Mu value
as one literal root atom. It calls the same stored value under the same
environment at the same common heap. Determinism gives the same output.
It does not infer equality of different Mu records from their bodies,
metadata, language, or observations. Nested Mu syntax remains opaque here.

Ordinary rows use a different argument. `node_warm` exposes every actual
original row and its ordered stored child calls. `RowCalls` retains the
literal edge constructor and full returned fields. `row_unique` compares
two sequences with the same original children and the same environment.
Both sequences replay at the exact common heap. Their exact child list
and actual edge constructor determine one row. This retains full guards,
symbols, ordered children, and row survival. It is not an atom-only proof.
Closed node shortcuts use the earlier complete original-row expansion.
They do not assume that Ready makes the original row order canonical.

For a root union, `raw_parts` constructs its actual ordered member calls
with `StoredUnionObservations.complete`. The parent warm equation and
actual constructor growth put the member-call endpoint below the common
reader. `StoredCallsReplay.replay` then obtains exact warm member calls.
Normal flatness makes those stored members atomic at the root. The proof
uses actual member reconstruction and literal union laws. It does not
assume physical reconstruction/union commutation.

`warm` has explicit warm call equations at one common Ready heap. It is a
completed-call component. `initial` closes that completion boundary:
initial Ready, availability, replacement availability, and SameParts
construct both sequential stored calls. The second call starts at the
first returned heap. Actual Keeps derives final Ready, availability,
growth, and both publication histories. Actual replay puts both outputs
at the exact final heap. No future call, reached range, desired output
law, or final heap is a premise of `initial`.

The proof does not transport SemanticReady through arbitrary Grows.
Each returned Ready comes from the actual reconstruction's Keeps receipt.
Grows is used only for actual replay and persistent record transport.

## Observations and physical Empty

`SameParts` compares exact literal root atoms and exact complete ordinary
rows. It ignores root union grouping, root row order, and multiplicity.
The ordinary row's full guard and ordered child records remain exact.

The reference-origin and row-origin decompositions use root union
flatness. Exact matched Mu atoms expose the same origins in any common
view heap. The view can be arbitrary because the theorem compares the
same complete atom in that one view; it does not claim execution or
unfold completion in an arbitrary view.

`same` obtains all finite observations from exact reference and row origins.
Each matched row uses reflexive ordered child observations. It retains
bare reference names even at depth zero.

The physical Empty argument has separate necessary normality facts.
Normal.proper excludes an ordinary node with no rows and gives a root
union members. Normal.flat and Normal.members ensure that a nonempty union
member supplies a literal atom or row. Thus an available root with no
parts must be literal Empty. A Mu stays a literal nonempty atom; the proof
does not infer its physical emptiness from semantic unfolding.

The public Normal and Available premises are explicit. Initial actual
reconstruction derives them at the final reader through Ready and Keeps.
No finite Cap, NoDeep condition, whole-forest closure, or global plain
heap premise is added.

## Constructed integration

The fixture builds an actual source from an empty heap with one bare
reference capture. Two root unions have different physical grouping.
One retains the bare reference beside two separate ordinary nodes. The
other groups those ordinary rows before adjoining the same bare reference.
Actual warm makeUnion equations derive SameParts. The roots are proved
physically unequal.

The replacement is a source-built productive raw Mu. The ordinary rows
retain both Bool guards and an ordered repeated-child row. The fixture
derives initial Ready, availability, and replacement availability, then
invokes `initial`. It retains both sequential stored equations, the exact
final warm replays, Keeps, availability, and both histories. It proves
SameParts and Related for the results. Both results are positive unions
and remain physically unequal. Thus the relation is not checked only on
empty results or identical physical outputs.

The public integration is an exact typed alias to the checked private
initial witness. Its public source begins with the exact strict fixture
bytes. It is not an uninstantiated alias to the general producer.

## Remaining boundary

Initial SameParts is still a substantive input. Exact Mu atom equality and
exact child records are stronger than observation equality. The theorem
does not derive SameParts for different raw body and ordinary-marker
callbacks from their writer history. It does not close the active binder,
root self-filter, or chronological earlier-winner induction. It also does
not claim physical root equality, general outer completion, or host runtime
correspondence.

## Existing validation inspected

- `literal-observations-direct-3`: genuinely zero-byte strict log.
- `literal-congruence-direct-3`: genuinely zero-byte strict log.
- `literal-observations-canonical-1`: terminal zero, 566 jobs, no warnings.
- `literal-congruence-canonical-1`: terminal zero, 583 jobs, no warnings.
- `literal-observations-public-1`: two complete public pairs.
- `literal-congruence-public-1`: two complete public pairs.
- `literal-congruence-kernels-1`: genuinely zero-byte strict log.
- `literal-congruence-kernels-public-1`: one complete constructed pair.

All selected public groups contain all eight required options, explicit
`#check @`, full `#print`, and `#print axioms`. No omission, printer failure,
warning, error, sorryAx, or truncation occurs. Only propext,
Classical.choice, and Quot.sound appear. Each inner worker reports
MemoryMax and MemoryHigh of 4294967296 bytes and zero swap.

The review checks four existing public pairs and one existing constructed
pair. It adds zero new pairs and repeats zero builds. The manifest pins
only final production, relevant dependencies, selected immutable evidence,
and this review's own report and verifier.
