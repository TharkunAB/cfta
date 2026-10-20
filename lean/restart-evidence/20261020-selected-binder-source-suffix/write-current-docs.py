from pathlib import Path
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261020-selected-binder-source-suffix'
block = '''## Current historical binder children and actual source suffixes

Updated: 2026-10-20 17:21 CEST. Proof checkpoint: `f10895e3d`.
Verified start: `7471f93f8`. Main remains `9769fe3e9`.
Read `lean/notes-current-selected-binder-source-suffix.md`.
An actual completed source build now derives its selected complete Mu's
historical rooted publication and raw source-child Origin, or the exact
initial complete cell. The same event retains its payload, key, actual
raw callback, self filter, Context, Reached and all issued intervals.
No caller-supplied writer or current-callback identity is assumed.

The same SourceRow now derives a nonunion terminal source receipt with
its Context, rooted entry, generic structural Syntax bound, and physical
and issued suffix to the supplied source return. Actual union tails and
makeUnion work derive that suffix. A terminal binder's selected full cell
can move forward by its nodeRecords retention. Any later reader interval
must still come from its actual call receipts.

Two public declarations and two actual examples pass complete statement,
proof and standard-axiom readback. All four selected strict logs are empty.
The default build passes 3487 jobs and 74042 axiom checks. Its sole warning is the
earlier ClosedCompletion unused-input warning. The examples check a
different-syntax warm requester and two source unions with later allocation.
Returned existential receipts stay separate from computed witness identities.

The next gap is the original-root ancestry of native encoded builds with
nonempty initial leaf captures and prior full Mu cells. A closed leaf or
whole self Mu is not itself an original binding certificate. General
ancestry, global renewal, active-owner exclusion, outer completion,
convergence and Haskell refinement remain open. Conditional root-language
and Sized laws are unchanged. All268Haskellfiles/all207activepackagefiles
retain their bytes. FINDINGS keeps external repairs first. No new Haskell
repair or validation is claimed. The full-library goal stays active.
Publication to formalize is authorized.

'''.replace('All268Haskellfiles/all207activepackagefiles', 'All 268 Haskell files and all 207 active package files')
(HERE / 'current-status-block.md').write_text(block)
paths = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md']
for name in paths:
    p = ROOT / name
    head, tail = p.read_text().split('\n\n', 1)
    p.write_text(head + '\n\n' + block + tail)
entry = '''Current proof update: 2026-10-20 17:21 CEST. Proof checkpoint: `f10895e3d`.
The actual completed source build derives the selected historical writer's
same-event raw SourceRow and child Origin, or its exact initial full cell.
SourceRow now derives its nonunion terminal receipt and actual physical
and issued suffix to the supplied source return. This supports full-cell
retention from that terminal binder. Native generated initial captures
still need their original-root ancestry. General renewal, outer completion,
convergence and Haskell refinement remain open. No new Haskell repair or
validation is claimed. All 268 Haskell files and all 207 active package
files retain their bytes. Default build: 3487 jobs and 74042 axiom checks. Read
`lean/notes-current-selected-binder-source-suffix.md`. Preserve every
external repair, reproducer and validation result below.

'''
(HERE / 'findings-update.md').write_text(entry)
p = ROOT / 'FINDINGS.md'
s = p.read_text()
anchor = 'Current proof update: 2026-10-20 17:00 CEST.'
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, entry + anchor, 1))
addition = '''An actual completed build now derives a selected complete Mu's same
historical publication, raw callback/filter and rooted source-child Origin,
or the exact initial full cell. SourceRow also derives a nonunion terminal
source receipt with its Context, Reached, generic Syntax bound and actual
physical/issued suffix to the supplied source return. Its terminal binder
cell moves forward by nodeRecords retention. Native encoded roots with
nonempty mapped captures still need an original-root ancestry certificate.
No general renewal, outer completion or Haskell refinement is added.

'''
(HERE / 'system-claim-update.md').write_text(addition)
p = ROOT / 'lean/notes-current-system-claim.md'
s = p.read_text().replace('Read `notes-current-rooted-indexed-source-children.md` for the latest proof checkpoint.',
                         'Read `notes-current-selected-binder-source-suffix.md` for the latest proof checkpoint.', 1)
anchor = '## Constructed root guarantee\n'
assert s.count(anchor) == 1
p.write_text(s.replace(anchor, addition + anchor, 1))
note = '''# Selected historical binder children and actual source suffixes

Proof checkpoint:f10895e3d. Verified start:7471f93f8. Main:9769fe3e9.
The ff-only refresh imports no change.

SourceCurrentSelectedBinderChildResume.selected_body_child_or_prior consumes
one actual completed source build and its original rich Context. It also
takes the exact complete Mu selected at that build's return, a full parent
row in its stored body and an exact ordered child lookup. It derives the
same complete initial cell or a historical publication rooted in that
actual build. No Written, desired child Origin or winner ancestry is a premise.

The new-writer branch retains the same event from written_body_origin.
Its complete entry/body/depth/ordinary fields and key remain equal to the
selected cell. It keeps first-write absence, all actual issued callback
paths, physical and issued suffix, historical raw build and self filter,
allocated Context, callback Reached, RowAt and SourceRow. That same raw
SourceRow derives Origin for the same full row, child index and child.
The historical expression can differ from the current warm requester's
expression. It has no strict bound against that requester by assumption.
The exact initial full-cell alternative stays explicit.

SourceCurrentSourceRowTerminalSuffix.terminal_source consumes an actual
SourceRow and its original Context and Reached. It derives a nonunion
terminal SourceRow for the SAME full row, with its actual call heaps,
Context, rooted entry, generic structural Syntax bound and actual suffix.
Node, capture and binder cases retain their own receipt and reflexive
suffix. A source union follows its actual selected member call. Its actual
prefix derives forward Reached. The member return Context supports the
remaining buildMany suffix. makeUnion correctness supplies the final
constructor interval. These two intervals compose with the same returned
terminal receipt for both physical Grows and issued-name Extends.

The suffix ends at exactly the supplied SourceRow.after. It does not
identify the terminal with an arbitrary earlier Origin proof or supply an
interval to an unrelated later reader. A terminal binder's selected full
cell moves to that source return through suffix.nodeRecords. The first
theorem can then consume that exact whole-return cell. This composes real
receipts; it assumes no desired historical ancestry or History transport.
Any later raw-callback filter, publication or outer interval must use its
own actual retained call receipts. The generic Syntax bound uses default
Symbol/Guard sizes. It is not a generated-value or full-self decrease.

The first actual example builds a raw used Mu with row5[leaf17,self]. A
different source binder wraps the same source body twice in a union. Its
actual Depth and ordinary probes return the same profiles and heap. Its
request reuses the same complete cache cell. The actual whole empty-start
build invokes selected_body_child_or_prior and excludes the initial arm.
The returned same-event/raw/SourceRow/Origin tuple remains intact. It is
not identified with an independently computed publication or expression.
A second application starts at the actual warm heap. Its proposed new
same-key event would retain the prior cell into event.afterBody, which
contradicts that event's first-write absence. Thus its exact initial-cell
arm is derived. No desired writer or Origin is assumed.

The second actual example has two source-union calls. Row5 has two equal
leaf17 children; later source members allocate row99 and row100. The
normalized raw value is an ordinary node. Its completed root call derives
the full row5 SourceRow. One terminal_source application retains the exact
returned terminal SourceRow, nonunion condition, Context, Reached, generic
bound and both suffix relations. A separate computed allocation-count
inequality shows node5's return differs from the whole return. The example
does not identify that computed node return with existential terminalAfter.

Both official strict logs and both constructed strict logs are empty.
Canonical builds and both public and both constructed complete
statement/proof/standard-axiom readbacks pass. Root personally observed
Audit handle34820 terminal0:3487jobs74042dependencies. Only the earlier
ClosedCompletion unused-input warning remains. All entered Lean jobs use
pinned Lean4.34.1, actual4GiB max/high, zero swap and five-minute caps.
A root setup command used an incorrect verifier filename before installing
the suffix source. It failed before Lean; its corrected setup and the
actual Lean attempts remain distinct. Reviews add no Lean job or proof pair.

The next substantial obligation is the original-root source ancestry of
native encoded builds. The original Fresh build can have empty inputs.
Later encoded builds use mapped closed leaves and complete self Mu values
as nonempty initial captures. original_slot identifies their exact initial
slot; native lookup identifies the exact closed leaf or full self Mu.
Those facts do not by themselves link the generated root to the original
program or prove a strict original binding decrease. Initial warm cells
need their own earlier construction receipt. Keep the original root,
generated root, selected historical expression and current callback distinct.

Native memo History stays at its checked captured reader. Original source
and canonical row positions, ordered children, leaf occurrences and first
encoder slots remain distinct. General ancestry, global renewal, all-owner
exclusion, outer completion, convergence and concrete Haskell refinement
remain open. Conditional root-language and Sized laws are unchanged.
Ordered enumeration, templates, subsumption, replaceRows and external
adapters retain separate implementation gaps.

No Haskell or active package file changes. FINDINGS keeps external repairs
first. The Typing documentation candidate remains unvalidated after its
cached-toolchain blocker. The full-library goal stays active. Publication
to formalize is authorized.
'''
(ROOT / 'lean/notes-current-selected-binder-source-suffix.md').write_text(note)
next_step = '''# Next native generated captures and original-root ancestry

The selected historical writer resume and actual terminal source suffix
are proved. Do not repeat them. Focus SourceRow while its actual source
union tails remain. The same terminal SourceRow carries its suffix to the
supplied source return. In its binder arm, suffix.nodeRecords retains the
same complete selected Mu there. The actual completed root call then
derives that selected historical writer or the exact initial full cell.
Any later filter/publication/outer interval must use actual call receipts.

The remaining substantial bridge concerns native encoded initial inputs.
An original closed Fresh build starts with empty captures and no initial
Mu cells. Its Reached paths stay rooted in the original syntax. A later
native encode build has a generated syntax root, mapped closed-leaf/full
self-Mu inputs and earlier full cache cells. Empty-initial exclusion does
not apply to those inputs. An exact capture slot or mapped self split is
not itself a certificate rooted in the original program.

Use the actual native leaf lookup, pure first ordinary-child Cut, source
row producer and rooted source child receipts to find the missing link.
Keep the original root, generated root, earlier writer and requester distinct.
Retain the same full row, ordered child, leaf occurrence and encoder slot.
Do not infer a full-self size decrease or transport memo History by Grows.
Do not add desired original ancestry as a premise to its own producer.

General renewal, active-owner exclusion, outer completion, convergence and
Haskell refinement remain open. Preserve all proofs, counterexamples,
repairs, drafts, stashes and worktrees. Record Haskell repairs first in
FINDINGS for external work. The full-library goal stays active.
'''
(HERE / 'next-binding-ancestry-handoff.md').write_text(next_step)
composition = '''# Composition after historical writer resume and source suffixes

Pure Cut retains the indexed first ordinary child through stored values.
source_cases derives SourceRow for its same full parent row. The rooted
child producer handles actual source node calls or exact capture/binder
stops. terminal_source now retains a same-row nonunion source receipt and
its actual physical/issued suffix. selected_body_child_or_prior derives
the same historical publication and raw child Origin from a selected whole
return cell. Its exact initial-cell alternative remains.

These pieces close the previously missing local-source-return suffix
producer. They do not yet label native generated roots with original
program binding ancestry. Native mapped inputs can contain closed leaves
or whole self Mu values. Their exact slots and native lookup split remain
available, but their original-root certificate is a separate obligation.
Inspect the live source audit before choosing that bridge's minimal API.

Global renewal, all-owner exclusion, outer completion, convergence and
Haskell refinement remain open. Native memo History stays at its checked
captured reader. No arbitrary forward reader transport is added.
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
add('lean/notes-current-selected-binder-source-suffix.md', note)
add(str((HERE / 'next-binding-ancestry-handoff.md').relative_to(ROOT)), next_step)
add(str((HERE / 'next-source-leaf-general-composition-review.md').relative_to(ROOT)), composition)
(HERE / 'source-doc-ranges.json').write_text(json.dumps({'ranges': ranges}, indent=2) + '\n')
print(json.dumps({'current_ranges': len(ranges), 'proof_checkpoint': 'f10895e3d'}))
