from pathlib import Path
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-rooted-indexed-source-children'
block = '''## Current rooted indexed source children and exact stops

Updated: 2026-10-20 17:00 CEST. Proof checkpoint: `3e69e40a1`.
Verified start: `29afe07fc`. Main remains `9769fe3e9`.
Read `lean/notes-current-rooted-indexed-source-children.md`.
An actual RowCall now derives its exact indexed original child call,
ordered prefix and suffix, joint Context, and forward physical and issued
growth. Its source result can be closed. The strict bound counts original
Syntax with default Symbol/Guard sizes, not generated physical values.

The same rooted SourceRow now derives either that actual child call and
Reached at its entry, an exact variable capture, or an exact selected Mu
body stop. Actual source-union prefixes carry the rooted route forward.
The same full parent row and ordered child index remain throughout.
No desired child ancestry or historical writer receipt is a premise.

Three public declarations pass complete statement, proof and standard-axiom
readback. Both official strict logs are empty. The default build passes
3485 jobs and 74039 axiom checks. Its sole warning is the earlier
ClosedCompletion unused-input warning. An actual closed source node in an
open normalized union retains repeated equal children at distinct indices.
Its selected child keeps the actual rooted call and source syntax bound.

The next step must recover a selected binder's own historical publication.
An exact initial full cache cell remains an alternative. A binder stop's
local return heap is not the enclosing return heap. Their actual suffix
growth still needs a producer before the selected cell can move forward.
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

entry = '''Current proof update: 2026-10-20 17:00 CEST. Proof checkpoint: `3e69e40a1`.
An actual RowCall now derives its indexed original child interval, Context,
physical and issued growth, and generic structural Syntax bound. A rooted
SourceRow follows actual source-union calls to that same child and rooted
entry, an exact capture, or an exact selected binder body stop. Closed
source node results are supported. The selected historical writer and
local-stop-to-enclosing-return suffix remain the next obligations. General
ancestry, renewal, outer completion, convergence and Haskell refinement
remain open. No new Haskell repair or validation is claimed. All 268
Haskell files and all 207 active package files retain their bytes.
Default build:3485jobs74039axiomchecks. Read
`lean/notes-current-rooted-indexed-source-children.md`. Preserve every
external repair, reproducer and validation result below.

'''
(HERE / 'findings-update.md').write_text(entry)
p = ROOT / 'FINDINGS.md'
s = p.read_text()
anchor = 'Current proof update: 2026-10-20 16:49 CEST.'
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, entry + anchor, 1))

addition = '''An actual indexed source RowCall now retains its ordered child interval,
joint Context, separate forward physical and issued growth, and strict
generic original Syntax bound. Its result can be closed. A rooted SourceRow
follows actual source-union prefixes to that same child and rooted entry,
an exact capture, or a selected binder body stop. A binder stop does not
identify the current callback with an earlier writer. Its local return
heap still needs an actual suffix to the enclosing return heap. General
original binding ancestry and a global recursive decrease remain open.

'''
(HERE / 'system-claim-update.md').write_text(addition)
p = ROOT / 'lean/notes-current-system-claim.md'
s = p.read_text().replace('Read `notes-current-indexed-first-ordinary-cut.md` for the latest proof checkpoint.',
                         'Read `notes-current-rooted-indexed-source-children.md` for the latest proof checkpoint.', 1)
anchor = '## Constructed root guarantee\n'
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, addition + anchor, 1))

note = '''# Rooted indexed source children and exact stops

Proof checkpoint:3e69e40a1. Verified start:29afe07fc. Main:9769fe3e9.
The ff-only refresh imports no change.

SourceCurrentIndexedRowCallChildren.indexed_child consumes an actual RowCall,
its original joint Context, and an exact selected output-child lookup. It
derives the same original child syntax index and actual child output index,
the exact ordered child prefix/build/suffix with adjacent heaps, and joint
Context at the child's actual entry. It accepts closed source node results.
It assumes no desired child-call or binding ancestry receipt.

The actual source-row prefix derives joint Context at the selected row.
The actual earlier child calls derive Context at the selected child. These
same two prefixes derive physical Grows and issued-name Extends separately.
Their composition ends at the child's entry heap. Verified.history here
means issued-name extension. It is not native publication memo History.
The theorem supplies no reader transport or reverse heap relation.

The strict source bound follows from the actual child syntax membership
in its original edge and the actual edge membership in the supplied node.
Syntax uses instSizeOfDefault for Symbol and Guard. Concrete payload sizes
are ignored. This is not a generated-value, cached-depth, self-Mu or outer
recursive-execution decrease. Original source and canonical row indices
remain distinct. Equal children keep their ordered occurrence indices.

SourceCurrentRootedRowChildOrigins.from_source_row consumes the actual
SourceRow, its original Context and Reached route, and the exact selected
child of that same complete parent row. It derives Origin with three arms.
The node arm retains actual buildEdges/makeNode/canonical row receipts,
the exact original RowCall and child interval, Context, forward physical
and issued growth, Reached at child entry, and a strict bound against the
original supplied expression. The capture arm retains the exact variable
slot, captured full value and structural row, selected child and Reached.
The binder arm retains its actual Depth/ordinary probes, request, selected
complete Mu cell, smart finish, stored-body row, selected child and Reached.

SourceRow.union recursion follows actual original source member calls.
The completed member prefix derives forward growth to its entry, so the
existing Reached.union/grows laws give the same rooted route there. The
same full parent row and child index remain fixed. The private induction
keeps the outer original Syntax bound across smaller source unions.
No original source member is identified with a normalized stored member.
The earlier pure Cut can supply the parent row and exact selected child.

An exact capture can later use Reached's source Path with original_slot.
An initial empty input list excludes row-bearing captures for that same
root. Later native encoded builds have nonempty mapped initial inputs.
Their exact row-bearing entries split into an unchanged closed leaf or a
complete self Mu. Neither arm gives a general source decrease by itself.

A binder stop can select an earlier writer with different body syntax.
Its Origin receipt does not export a terminal binder size bound against
Origin.original. It also does not export physical growth from that local
binder return heap to the enclosing source call's return heap. Reached
supplies earlier crossing growth, not this later suffix. A historical-writer
resume theorem can require the exact selected cell at the enclosing return.
Automatic consumption of a local stop must first derive its actual suffix
while the original SourceRow union tails and makeUnion calls remain present.
This missing producer is explicit. No arbitrary history transport is used.

The constructed witness builds a closed ordinary source node with row5
and equal leaf17 children at indices0 and1. That node is the first source
member of an actual union whose other member is the external Depth input.
The union result is open. The actual completed whole build derives SourceRow
for the same full row5. One from_source_row application at child index1
retains the actual rooted source-child call. The generic source-size bound
is kept explicitly with default Symbol/Guard instances. The example needs
no Ready, replay, desired Origin premise or assumed later history.

Both official strict logs are empty. Canonical builds and all three full
public statement/proof/standard-axiom readbacks pass. The constructed strict
and full proof checks pass. Root personally observed Audit handle30743
terminal0:3485jobs74039dependencies. Only the earlier ClosedCompletion
unused-input warning remains. All actual Lean jobs use pinned Lean4.34.1,
4GiB memory max/high, zero swap and a five-minute cap. Failed elaborations,
drafts and independent reviews remain. Reviews add no Lean job or proof pair.

The next actual selected-writer producer should compose build_writer_or_prior,
written_body_origin and from_source_row. It must retain the exact initial
full-cell alternative or the same event's payload, historical raw build,
self filter, Context, Reached, SourceRow and indexed Origin. It must take
the selected full cell at the actual completed build's return. It must
not assume caller-supplied Written or equate current and earlier callbacks.
Its proof would not close the separate local-stop suffix obligation.

General original-program ancestry for generated encode syntax, native
full-self reentry, global renewal, all-owner exclusion, outer completion,
convergence and concrete Haskell refinement remain open. Native memo History
stays at its checked captured reader. Conditional root-language and Sized
laws are unchanged. Ordered enumeration, templates, subsumption, replaceRows
and external adapters retain separate implementation gaps.

No Haskell or active package file changes. FINDINGS keeps each external
repair first. The Typing documentation candidate remains unvalidated after
its cached-toolchain blocker. The full-library goal stays active. Publication
to formalize is authorized.
'''
(ROOT / 'lean/notes-current-rooted-indexed-source-children.md').write_text(note)

next_step = '''# Next selected historical writer and actual stop suffix

The generic RowCall indexed child extractor and rooted SourceRow Origin
producer are proved. Do not repeat them. Closed source node results are
supported. Actual original source-union prefixes retain Reached forward.
The same full parent row and child occurrence remain fixed.

The next small producer can consume one actual completed source build,
its original Context, an exact full Mu cell selected at its return,
RowAt of its stored body, and an exact selected child. Compose
build_writer_or_prior, written_body_origin and from_source_row.
Derive either the same complete initial cell or the same rooted historical
publication's raw callback/filter/Context/Reached/SourceRow and child Origin.
Keep the same event, payload, key and all issued and physical intervals.
Do not take caller-supplied Written or desired binding ancestry as a premise.

This producer needs selected-at-whole-return. Origin.binder only exposes
selected-at-local-return. It forgets the later union tails and makeUnion
suffix. Derive local-after to enclosing-after Grows from actual SourceRow
calls before moving that selected record forward. Reached gives no such
suffix. A later reader's memo History gives no such suffix either.

Captures can use Reached's original source Path and original_slot. Native
initial inputs can be mapped closed leaves or complete self Mu values.
Preserve exact source slots and leaf occurrences. Do not identify a first
encoder slot with a repeated occurrence. Full-self reentry gives no strict
original syntax decrease. Initial warm full cells remain an explicit stop.

General ancestry, renewal, outer completion and Haskell refinement remain
open. Preserve all older proofs, counterexamples, repairs, drafts, stashes
and worktrees. Record Haskell repairs first in FINDINGS for external work.
The full-library goal stays active.
'''
(HERE / 'next-binding-ancestry-handoff.md').write_text(next_step)
composition = '''# Composition after rooted indexed source children

Pure Cut retains an exact leaf occurrence, parent row, child and inner
leaf index through stored union/Mu prefixes. source_cases derives SourceRow
for that same complete row from the actual original source build.
from_source_row now derives an actual rooted child or capture/binder stop.
Its node child has a strict original generic Syntax bound.

Resume a selected historical binder only from an actual selected full cell
at the whole build return. Preserve the initial-cell alternative. The same
writer event must supply its historical raw build, self filter, Context,
Reached and SourceRow before the new child Origin is derived.
The local binder stop still needs its actual suffix to that whole return.
These are separate producers. Do not collapse their heap endpoints.

For captures, use the actual rooted source Path to recover the original
suffix slot. Native exact mapped slots then split into closed leaf/full
self Mu. General closed-leaf ancestry and full-self reentry still need an
original-program measure. Native memo History stays at its captured reader.
No global renewal, outer completion, convergence or Haskell refinement
is added by this checkpoint.
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
add('lean/notes-current-rooted-indexed-source-children.md', note)
add(str((HERE / 'next-binding-ancestry-handoff.md').relative_to(ROOT)), next_step)
add(str((HERE / 'next-source-leaf-general-composition-review.md').relative_to(ROOT)), composition)
(HERE / 'source-doc-ranges.json').write_text(json.dumps({'ranges': ranges}, indent=2) + '\n')
print(json.dumps({'current_ranges': len(ranges), 'proof_checkpoint': '3e69e40a1'}))
