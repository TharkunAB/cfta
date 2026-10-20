# Indexed first ordinary-child cuts and actual source rows

Proof checkpoint:e2175de1e. Verified start:f9c6d7ea6. Main:9769fe3e9.
The ff-only refresh imports no change.

SourceCurrentIndexedFirstOrdinaryCut.split consumes an exact leaves(raw)
lookup and RowAt of the selected leaf. It derives either that same row in
raw or an indexed Cut to the first ordinary parent row and ordered child.
The pure value theorem uses no heap, lexical Context or source expression.
It follows the actual leaves definition. A closed value returns itself as
its sole leaf. Empty and reference values cannot supply a structural row.

Cut.node retains an open ordinary value, its exact canonical row lookup,
ordered child lookup, inner leaf lookup and flattened prefix equation.
Cut.union retains an open stored union's actual member index, its prefix
leaf count and the nested cut. Cut.mu retains an open full Mu's actual
stored body at the same leaf index. Cut.facts derives RowAt raw parentRow
and the exact child and inner leaf lookups from the same cut witness.
The private proof uses structural induction on finite stored values. Its
internal size bound is not a public recursive reduction decrease.

SourceCurrentIndexedLeafSourceRows.source_cases composes that pure split
with the existing actual build_row_origin theorem. Its premises are the
original rich Context, actual completed source build, exact leaf lookup
and RowAt of that leaf. The direct arm derives SourceRow for that same
row. The cut arm derives SourceRow for cut.facts.1's same full parent row.
The original expression, inputs, before heap, raw result and after heap
remain identical. Desired source ancestry is not an input assumption.

Stored union positions are not original source union positions. The model
normalizes union members. The previous checked counterexample shows that
same-leaf descent through original source members is false even as a
membership claim. Full row identity permits build_row_origin to recover
the actual source route. SourceRow.union contains actual original member
calls. Cut.union contains actual normalized stored members. Do not identify
these two routes or their indices.

The constructed witness first completes a closed raw Mu with row19. An
open raw Mu follows it. Its body has row7 and ordered children consisting
of leaf17, its own reference, the external Depth reference and leaf17.
The actual root union has equal leaf17 occurrences at indices1 and4.
The computed cut crosses stored union member1, the open Mu body, body row0
and child3, with inner index0. This cut is recorded independently.

One source_cases application at occurrence4 retains its returned Cut and
the same SourceRow together. A direct row17 in raw is impossible: the raw
root's structural rows are19 and7. Thus the returned parent row differs
from the selected leaf's row. The witness does not identify its returned
existential cut with the independently computed cut. A separate closed
leaf root exercises the direct stopping arm.

Both official strict logs are empty. Canonical module builds and all four
complete public statement/proof/standard-axiom readbacks pass. The selected
constructed strict log is empty and its FULL1 readback passes. Root Audit
handle28640 was personally observed terminal0:3483jobs74034dependencies.
The only warning is the earlier ClosedCompletion unused-input warning.
All entered Lean jobs use pinned Lean4.34.1 and actual4GiB max/high with
zero swap and a five-minute cap. One prototype wrapper stopped at a
systemd bus denial before Lean. Its raw failure remains separate from the
actual Lean job count. All failed elaborations and drafts remain preserved.
Reviews and integrity checks add no Lean job or public proof pair.

The next producer must eliminate SourceRow to an actual original child
call or an exact capture/binder stop. A generic RowCall child extractor
must accept closed source node results: a normalized outer result can be
open even when the original source node is closed. It must retain the
same ordered child index, actual child prefix/build/suffix, rich Context,
forward physical and issued growth, and generic structural Syntax bound.
That bound uses default Symbol/Guard sizes and ignores their payload size.

A rooted node arm can then derive Reached at the actual child entry.
Capture and binder arms remain exact stops. A variable must retain its
actual original slot. A selected warm Mu retains its original historical
publication and full stored body. Neither arm supplies a general decrease
by assumption. Original program ancestry for generated encode syntax,
global renewal, all-owner exclusion, outer completion, convergence and
concrete Haskell refinement remain open. Native memo History stays at its
checked captured reader. Physical heap growth does not transport it.

Conditional constructed-root language equality and Sized laws are unchanged.
Ordered enumeration, templates, subsumption, replaceRows and external
adapters retain separate implementation gaps. No Haskell or active package
file changes. FINDINGS keeps each external repair first. The Typing
documentation candidate remains unvalidated after its cached-toolchain
blocker. The full-library goal stays active. Publication is authorized.
