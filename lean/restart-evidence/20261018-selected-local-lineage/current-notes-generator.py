from pathlib import Path
import datetime,json
from zoneinfo import ZoneInfo
R=Path('/home/tritlo/Code/mcfta');E=R/'lean/restart-evidence/20261018-selected-local-lineage'
a=json.loads((E/'checkpoint-validation.json').read_text());proof=a['proof_commit'][:8]
now=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
pub=a['new_public_pairs'];con=a['constructed_pairs'];groups=a['groups'];entries=a['component_entries']
section=f'''## Current selected local row origins and immediate descent

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `ff10965d`. Main source remains `c0cc8a05`.
Read `lean/notes-current-selected-local-lineage.md` for exact boundaries.

Actual retained Scan records now supply their original selected Root from
literal false primary returns. No heap, memo or replay law is needed for
that value property. Original source paths derive actual Required compiler
absence through canonical selected-path sorting and duplicate removal.

The complete actual local class worker now derives indexed row origins
without a supplied Root or compiled-absence premise. Selected slots use
actual primary support. Untouched slots retain their complete value through
Required and the class fold, or become Empty during final propagation.
Constrained recursive inputs are permitted in the untouched branch.

The full allocated local reducer now derives the same result through actual
field lookup, accessor, precheck, Scan, Required and class passes. The raw
input guard's unselected footprint and successful worker equation remain
explicit. Positive surviving rows retain the full indexed input row and the
exact continuation child. That child has strictly smaller mass than its
explicit immediate source node. The source node can be reconstructed;
proper initial-source occurrence and a global decreasing rank remain open.

Full Audit passes 3221 jobs and 70817 checks. Five production and five
constructed strict logs are empty. All {pub} public and {con} constructed
full pairs pass in {groups} groups with all eight settings and standard
axioms. Audit peak is 375 MiB under 4 GiB maximum/high and zero swap.
Evidence is in `lean/restart-evidence/20261018-selected-local-lineage/`.

Next lift the local origin through actual Parent construction and native
optional-binder/writer reconstruction. Prove proper original occurrences,
all-owner separation and a finite fresh-call bound or a well-founded rank.
General recursive completion, recursive outer language preservation,
used-writer alignment, repeated convergence and public Haskell correspondence
remain open. The complete finite ordinary outer domain is unchanged.
No Haskell patch or new production defect is added. Field-pool b9219b9e
remains fixed in c0cc8a05. Keep the FINDINGS repair registry first.
Publication awaits the pending direct approval. Do not retry or bypass it.

'''
anchor='## Current actual positional lineage and primary support\n'
for name in ['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md']:
 p=R/name;s=p.read_text();assert section.splitlines()[0] not in s;assert s.count(anchor)==1;p.write_text(s.replace(anchor,section+anchor,1))
p=R/'FINDINGS.md';s=p.read_text();anchor='## Haskell fix handoff for external work\n\n';assert s.count(anchor)==1
entry=f'''Current proof update: {now}. Proof checkpoint is `{proof}`.
Actual local row origins now follow the raw guard, field lookup, precheck,
original Scan, Required and class passes. Actual selection derives Root;
source paths derive compiler absence. Untouched constrained Mu values need
no Root premise. Positive continuations strictly decrease mass below their
immediate source node. That node can be reconstructed, so no global rank
or proper initial-source occurrence follows. General recursive completion,
fresh-call bounds, writer alignment, recursive language preservation,
convergence and full public Haskell correspondence remain open.
Full Audit passes 3221 jobs and 70817 checks. No Haskell patch or new defect
is added. Field-pool repair `b9219b9e` remains fixed in `c0cc8a05`.
Read `lean/notes-current-selected-local-lineage.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

'''
p.write_text(s.replace(anchor,anchor+entry,1))
p=R/'lean/notes-proof-status-20261017.md';s=p.read_text();assert 'Checked at proof checkpoint `fe68c2e9`.' in s
s=s.replace('Checked at proof checkpoint `fe68c2e9`.','Checked at proof checkpoint `'+proof+'`.',1)
anchor='## Strongest current claim in plain technical English\n'
paragraph='''Actual full local row origins now follow the initial raw guard, its field
lookup and precheck, literal Scan, Required preparation and class passes.
Actual selection supplies Root. Source paths supply compiled absence.
Untouched constrained recursive values need no Root assumption. A positive
retained continuation has smaller structural mass than its explicit immediate
source node. That node can be reconstructed. General initial-source descent
and a global recursive rank remain open. The successful worker equations
and initial raw footprint stay explicit. Read
[the current checkpoint](notes-current-selected-local-lineage.md).

'''
s=s.replace('[the current checkpoint](notes-current-actual-positional-lineage.md).','[the earlier checkpoint](notes-current-actual-positional-lineage.md).',1)
assert s.count(anchor)==1;p.write_text(s.replace(anchor,paragraph+anchor,1))
note=f'''# Selected local row origins and immediate descent

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `ff10965d`. Main source: `c0cc8a05`.
This is local proof progress. The full-library goal remains active.

## Strongest complete statement

For a validated finite explicit graph, including cycles, the checked model
lists exactly the distinct accepted finite terms at each node-count size.
Its counts are correct. Rank and unrank follow the specified order and are
inverses at valid indexes. Correct finite yes/no guard replies and the stated
ordering laws give these successful results. Finite unknown replies can
instead return an error. Supported closed resident Original operands have
exact recursive native intersection semantics. Initial resources construct
those executions. A complete finite ordinary constrained outer pass preserves
the full guarded language. That outer domain excludes Mu, references and
explicit unions in every descendant.

These are separate implementation-model results. They do not prove every
public Haskell operation terminates and meets its contract. Read
`notes-proof-status-20261017.md` for the full-library target.

## New completed components

SelectedRootOrigins derives the actual earlier false primary return for
every retained literal Scan record. Its selected original member path and
present source slot supply Root. No physical heap, memo correctness,
closure, coherence or replay premise is needed for this value property.
The theorem still requires a literal successful Scan return.

RequiredPathFootprints derives absent Required keys from complete source
path exclusion. Its general laws retain arbitrary signed paths. Its selected
record laws trace membership through canonical sorting, duplicate removal,
flattening and natural-to-signed conversion. The compiler absence is a
conclusion. Source path exclusions are initial input properties.

ActualLocalRowOrigins handles the complete actual local class worker.
Actual earlier Scan calls produce reached physical facts and the causal
Plain heap. Retained records inherit input coherence and path footprints.
If a retained class selects the tracked slot, its actual primary return
supplies Root. Source paths derive Required's absent continuation key.
The actual Required and class pass then supply the indexed row relation.

If no retained class selects the slot, Required and every literal class
retain the complete value. Final Empty propagation can erase it. This
branch permits arbitrary constrained Mu values. It does not claim they
satisfy Root. No desired future origin, semantic row reads, supplied Root,
or compiled-absence premise enters the complete local theorem.

ActualLocalReduceRowOrigins extends that result through the original raw
field load, accessor and equality precheck. The actual normalized load and
precheck derive the own records, coherence, original sort and reached
physical state. The initial raw guard's unselected footprint remains explicit.
Unchanged and Empty branches derive the row relation directly. The live
branch invokes the new actual local class theorem.

PositionalOriginDescent uses a positive own field to select an indexed
complete source row and the identical present continuation child. That
child has strictly smaller structural mass than its immediate source node.
The theorem needs no heap premise. Its anchor is explicit; it need not be
an occurrence in the first source program.

## Remaining work

The source footprint and successful worker equations remain explicit. No
new unrestricted recursive execution domain is asserted. Lift the origin
through actual Parent checked construction, including its sentinel cases.
Relate selected ordinary rows and continuations through native child
requests, optional binder construction, stored substitution and the real
earlier retained writer to proper occurrences in the initial source.

The frozen lineage-review explains the exact limit. Identical raw guards
and local child indexes do not identify an initial occurrence. Existing
OuterOriginalRepeat reconstructs an original value with a different inherited
key; its next call erases. It is not an infinite trace. It does not refute
the fixed untouched footprint. Native row traces expose exact child request
calls, but do not equate every returned child to either requested child.
The required ordered occurrence transport remains open.

Prove separation from every active owner and bound fresh recursive calls,
or construct a well-founded global rank. Local child mass decrease alone
does not do this when a later source node can be reconstructed. Complete
used-binder/earlier-writer alignment, recursive outer language preservation,
repeated convergence, concrete public adapters and Haskell correspondence.
The complete finite ordinary outer-pass domain is unchanged. Proof counts
do not supply a completion percentage or time estimate.

## Verification and preservation

Full Audit passes 3221 jobs and 70817 dependency checks. Only the unchanged
ClosedCompletion unused-variable warning remains. Five production and five
constructed strict logs have exactly zero bytes. All {pub} public and {con}
constructed pairs have full signatures, proofs and axiom reports in {groups}
groups. All eight required settings are enabled. Only standard axioms occur.
Effective maximum/high memory limits are 4 GiB. Swap maximum is zero.
The Audit peak is 375 MiB. Seven selected component manifests pin {entries}
entries. All numbered drafts and raw output files remain present.

The constructed cases cover repeated actual retained records, exact signed
compiler exclusion, a constrained Mu outside active class paths, positive
actual local rows, full precheck reduction and strict immediate continuation
descent. Each executed integration constructs its own initial facts.
Read the selected groups and component reviews for exact witnesses.
Evidence is in `restart-evidence/20261018-selected-local-lineage/`.

All 25912 starting files remain present. All 3215 older non-Audit Lean
sources, 242 Haskell files, 206 active-package files, two stashes and three
other worktrees retain their bytes or metadata. Audit only adds five imports.
The preservation report checks 134 frozen module manifests and 978 module
entries. No Haskell patch or new production defect is added. Field-pool
repair b9219b9e remains fixed at main c0cc8a05. Root FINDINGS keeps every
previous repair entry. Publication awaits the existing direct approval.
No push is attempted or retried.
'''
p=R/'lean/notes-current-selected-local-lineage.md';assert not p.exists();p.write_text(note)
print(json.dumps({'updated_at':now,'proof':proof,'files':9}))
