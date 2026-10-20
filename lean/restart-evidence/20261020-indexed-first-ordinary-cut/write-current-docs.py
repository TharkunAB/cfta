from pathlib import Path
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-indexed-first-ordinary-cut'
block = '''## Current indexed first ordinary-child cuts and source rows

Updated: 2026-10-20 16:49 CEST. Proof checkpoint: `e2175de1e`.
Verified start: `f9c6d7ea6`. Main remains `9769fe3e9`.
Read `lean/notes-current-indexed-first-ordinary-cut.md`.
An exact indexed row-bearing leaf now gives either its structural row in
the raw root or the first ordinary parent row and child crossing. The cut
retains the actual stored union member, open Mu body, child index, inner
leaf index and prefix offsets. Closed values stop at the whole value.

The same actual completed source build and rich Context derive SourceRow
for that same selected row or cut parent row. The cut and source receipt
share the full parent row. No source ancestry receipt is a premise.
Stored union membership does not identify an original source-union call.
Normalization can change the leaf lists of original source members.

Four public declarations pass complete statement, proof and standard-axiom
readback. Both official strict logs are empty. The default build passes
3483 jobs and 74034 axiom checks. Its sole warning is the earlier
ClosedCompletion unused-input warning. An actual union and open Mu example
retains repeated equal leaves at indices1/4. The returned cut keeps the
same SourceRow. Its parent row differs from the selected leaf's row.

The next producer must follow SourceRow to an actual indexed original child
call or an exact capture/binder stop. Its child extractor must also accept
closed source node results. Historical Mu writers retain their own events.
General ancestry, global renewal, active-owner exclusion, outer completion,
convergence and Haskell refinement remain open. Conditional root-language
and Sized laws are unchanged. All 268 Haskell files and all 207 active
package files retain their bytes. FINDINGS keeps external repairs first.
No new Haskell repair or validation is claimed. The full-library goal stays
active. Publication to formalize is authorized.

'''
(HERE / 'current-status-block.md').write_text(block)
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
for name in paths:
    p = ROOT / name
    head, tail = p.read_text().split('\n\n', 1)
    p.write_text(head + '\n\n' + block + tail)

entry = '''Current proof update: 2026-10-20 16:49 CEST. Proof checkpoint: `e2175de1e`.
An actual indexed row-bearing leaf now derives its root structural row or
the first ordinary parent row/child cut. Exact stored union/Mu prefixes,
child/inner indices and offsets remain. The same actual completed source
build derives SourceRow for that same row or parent row. The source child
or exact capture/binder stop remains the next obligation. Stored union
membership does not identify an original source-union call. General
ancestry, renewal, outer completion, convergence and Haskell refinement
remain open. No new Haskell repair or validation is claimed. All 268
Haskell files and all 207 active package files retain their bytes.
Default build:3483jobs74034axiomchecks. Read
`lean/notes-current-indexed-first-ordinary-cut.md`. Preserve every external
repair, reproducer and validation result below.

'''
(HERE / 'findings-update.md').write_text(entry)
p = ROOT / 'FINDINGS.md'
s = p.read_text()
anchor = 'Current proof update: 2026-10-20 16:19 CEST.'
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, entry + anchor, 1))

addition = '''For an actual indexed row-bearing leaf, the first ordinary-child cut now
retains the full parent row, exact child and inner indices, and stored
union/Mu prefix offsets. A direct structural root row is a separate arm.
The same completed source build derives SourceRow for the same selected
row or cut parent row. Closed values stop at the whole value. This derives
no original child call across captures or selected historical Mu writers.
Stored union members remain distinct from original source-union calls.

'''
(HERE / 'system-claim-update.md').write_text(addition)
p = ROOT / 'lean/notes-current-system-claim.md'
s = p.read_text().replace('Read `notes-current-open-ordinary-leaf-source-calls.md` for the latest proof checkpoint.',
                         'Read `notes-current-indexed-first-ordinary-cut.md` for the latest proof checkpoint.', 1)
anchor = '## Constructed root guarantee\n'
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, addition + anchor, 1))

note = '''# Indexed first ordinary-child cuts and actual source rows

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
'''
(ROOT / 'lean/notes-current-indexed-first-ordinary-cut.md').write_text(note)

next_step = '''# Next actual indexed source-child or exact stop

The pure Cut and source_cases producers are proved. Do not repeat them.
They preserve the exact selected leaf occurrence and SAME full parent row.
Their stored union route is not the original source-union call route.

First expose a generic actual RowCall indexed_child extractor without an
open-result premise. It must derive the exact original child syntax and
actual completed prefix/build/suffix, rich Context at child entry, forward
Grows and issuedExtends, and the generic default-size Syntax bound. The
earlier node_leaf endpoint cannot serve closed source node results.

Then eliminate an actual SourceRow under its original Context and Reached.
Use only node, capture and binder alternatives. The node arm retains the
actual RowCall and helper's same child index, and derives Reached at the
actual child entry. SourceRow.union follows its actual original member
prefix and transports Reached only through forward growth. Retain the
same full parent row and ordered child throughout that recursion.

The capture arm retains the exact variable lookup, row and selected child.
The binder arm retains its actual callbacks/request, selected complete Mu
cell, smart finish and stored-body row. It is a stop until the selected
writer's own rooted historical publication is recovered. Do not assume
that selected body is the current callback body. Do not add desired source
ancestry as an induction hypothesis or infer physical value decrease.

Prototype paths outside this frozen checkpoint are not selected official
proofs. Root must review, install and canonical-build each next module.
The complete default Audit must then pass under its actual capped handle.
Keep source/canonical row positions, child positions, leaf occurrences
and first encoder slots distinct. Native initial captures can be nonempty.
Native memo History remains at its checked captured reader.

Preserve all older proofs, counterexamples, repairs, drafts, stashes and
worktrees. Record Haskell repairs first in FINDINGS for external work.
General ancestry, renewal, outer completion and Haskell refinement remain
open. The full-library goal stays active.
'''
(HERE / 'next-binding-ancestry-handoff.md').write_text(next_step)
composition = '''# Composition after the indexed first ordinary-child cut

The actual leaves traversal now supplies its pure first-cut certificate.
The actual source build supplies SourceRow for the SAME complete row.
This closes the missing value geometry and source-row connection. The
previous union leaf-list counterexample still applies and remains stored.

Next expose actual RowCall child inversion independently of whether the
source node's result is open. Then use SourceRow's original source route
to derive an actual rooted child call or exact capture/binder stop. The
future node syntax bound must refer to the original supplied expression
with generic default Symbol/Guard sizes. It must not count a generated
physical body or claim ancestry for arbitrary encode syntax.

For captures, combine an actual rooted Path with original_slot. For a
selected binder, use its own same-event rooted Written/publication and
historical raw build/filter/Context/Reached receipt. Native mapped slots
already split into the exact closed leaf or whole selected self Mu.
These inputs do not yet prove a global original-program ancestry measure.

No global renewal, general active-owner exclusion, outer completion,
convergence or concrete Haskell refinement is added by this checkpoint.
'''
(HERE / 'next-source-leaf-general-composition-review.md').write_text(composition)

ranges = []
def add(path, text):
    s = (ROOT / path).read_text()
    assert s.count(text) == 1, path
    start = s[:s.index(text)].count('\n') + 1
    ranges.append({'path': path, 'start_line': start,
                   'end_line': start + len(text.splitlines()) - 1,
                   'text': text, 'sha256': hashlib.sha256(text.encode()).hexdigest()})
for p in paths:
    add(p, block)
add('FINDINGS.md', entry)
add('lean/notes-current-system-claim.md', addition)
add('lean/notes-current-indexed-first-ordinary-cut.md', note)
add(str((HERE / 'next-binding-ancestry-handoff.md').relative_to(ROOT)), next_step)
add(str((HERE / 'next-source-leaf-general-composition-review.md').relative_to(ROOT)), composition)
(HERE / 'source-doc-ranges.json').write_text(json.dumps({'ranges': ranges}, indent=2) + '\n')
print(json.dumps({'current_ranges': len(ranges), 'proof_checkpoint': 'e2175de1e'}))
