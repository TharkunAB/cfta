from pathlib import Path
import datetime,json
from zoneinfo import ZoneInfo
R=Path('/home/tritlo/Code/mcfta');E=R/'lean/restart-evidence/20261018-actual-positional-lineage'
report=json.loads((E/'checkpoint-validation.json').read_text())
proof=(E/'proof-commit.txt').read_text().strip()[:8]
now=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
jobs=report['audit_jobs'];deps=report['audit_dependency_checks'];peak=report['audit_peak_MiB']
public=report['new_public_pairs'];constructed=report['constructed_pairs'];groups=report['groups'];modules=len(report['production_modules'])
section=f'''## Current actual positional lineage and primary support

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `57ac518c`. Main source remains `c0cc8a05`.
Read `lean/notes-current-actual-positional-lineage.md` for exact boundaries.

Actual Required preparation and the subsequent literal class right fold now
compose indexed row origins from entry facts. A surviving row with a nonempty
own field retains a complete indexed input row and the exact child at each
unselected continuation index. The proof includes final Empty propagation.
The ordinary Edit law derives intermediate physical facts from actual calls.
It no longer needs supplied semantic row reads or future preservation laws.
Accepted recursive Head produces empty-own rows in a causal Plain heap.

Actual false primary selection now supplies the selected original value's
Root condition. Ordinary roots permit arbitrary constraints. Recursive roots
must pass the actual plain gate. Public smart Mu can contain constraints;
Root is not unconditional for all public inputs. The class law retains Root
through later selected below edits. Original selection and later edited
values remain distinct. Compiler coherence and the unselected footprint,
initial physical facts, and actual successful worker equations stay explicit.

Full Audit passes {jobs} jobs and {deps} dependency checks. All {modules}
production and {constructed} constructed strict logs are empty. All {public}
public and {constructed} constructed full pairs pass in {groups} groups with
all eight settings and standard axioms. Audit peak is {peak} MiB under
4 GiB maximum/high and zero swap. Evidence is in
`lean/restart-evidence/20261018-actual-positional-lineage/`.

The origins refer to the immediate input forest. Proper initial-source
occurrences through recursive reconstruction and native writers remain open.
All-owner separation and a bound on fresh calls or a well-founded measure
remain open. General recursive completion, recursive outer language
preservation, repeated convergence and full public Haskell correspondence
remain open. The complete finite ordinary outer domain is unchanged.
No Haskell patch or new production defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Keep the FINDINGS repair registry first.
Publication awaits the pending direct approval. Do not retry or bypass it.

'''
anchor='## Current outer guard transport and positional rows\n'
for name in ['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md']:
 p=R/name;s=p.read_text();assert section.splitlines()[0] not in s;assert s.count(anchor)==1
 p.write_text(s.replace(anchor,section+anchor,1))
p=R/'FINDINGS.md';s=p.read_text();anchor='## Haskell fix handoff for external work\n\n';assert s.count(anchor)==1
entry=f'''Current proof update: {now}. Proof checkpoint is `{proof}`.
Actual Required preparation and the class right fold now compose exact
indexed row origins and unchanged continuation children from entry facts.
Actual false primary selection supplies the selected original Root premise.
Public smart Mu does not imply the plain gate. This is a proof-support
boundary, not a Haskell defect. General recursive completion, fresh-call
bounds, original-source descent, used-writer alignment, recursive language
preservation, convergence and public Haskell correspondence remain open.
Full Audit passes {jobs} jobs and {deps} checks. No Haskell patch or new
production defect is added. Field-pool repair `b9219b9e` remains fixed and
validated in `c0cc8a05`. Read
`lean/notes-current-actual-positional-lineage.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

'''
p.write_text(s.replace(anchor,anchor+entry,1))
p=R/'lean/notes-proof-status-20261017.md';s=p.read_text();assert 'Checked at proof checkpoint `b4fcc918`.' in s
s=s.replace('Checked at proof checkpoint `b4fcc918`.','Checked at proof checkpoint `'+proof+'`.',1)
anchor='## Strongest current claim in plain technical English\n'
paragraph='''Actual Required preparation and the subsequent class right fold now
compose same-index full-row origins and exact unselected children from
initial physical facts. The ordinary Edit origin no longer requires
supplied semantic row reads. Accepted recursive Head yields empty-own rows.
Actual false primary selection supplies the selected original Root premise;
public smart Mu does not supply it for arbitrary values. The tracked Root
condition then survives the literal class fold. Compiler footprints and
successful worker equations remain explicit. These are immediate input
origins. Proper initial-source descent, all-owner separation and fresh-call
bounds remain open. Read
[the current checkpoint](notes-current-actual-positional-lineage.md).

'''
assert s.count(anchor)==1;p.write_text(s.replace(anchor,paragraph+anchor,1))
note=f'''# Actual positional lineage and primary support

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `57ac518c`. Main source: `c0cc8a05`.
This is local proof progress. The full-library goal remains active.

## Strongest complete statement

For a validated finite explicit graph, including cycles, the checked model
lists exactly the distinct accepted finite terms at each node-count size.
Its counts are correct. Its rank and unrank operations follow the specified
order and are inverses at valid indexes. Correct finite yes/no guard replies
and the declared ordering laws give these successful query results.
Finite replies that include unknown can instead stop with an error.

Supported closed resident Original operands have exact recursive native
intersection semantics. Initial resource bounds construct their executions.
A complete finite ordinary constrained outer pass preserves the full guarded
language. That outer domain excludes Mu, references and explicit unions in
every descendant. These are separate checked implementation-model results.
They do not prove every public Haskell call terminates and meets its contract.
Read `notes-proof-status-20261017.md` for the full target.

## New results

`SourceCurrentActualEditRowOrigins` derives full same-index pre-normalization
row origins from actual successful Edit calls. Initial SharedGood, available
original values and resident input rows supply intermediate facts. Surviving
normalized rows retain an input index and the exact child at each absent
child key. No semantic row inventory or per-call future invariant is given.
Other selected children can perform arbitrary recursive work.

`SourceCurrentClassPositionalFootprints` checks both path-prefix directions.
The tracked continuation excludes edits at that child, above it, or below it.
Coherent records derive the exact compiled child map. Actual class execution
selects either an unchanged forest value or a below edit with that child key
absent. The theorem retains actual prefix and suffix calls and full states.

`SourceCurrentActualPlainHeadOrigins` derives causal heap preservation and
empty effective own fields from accepted Head and Required calls. Its mixed
source fixture satisfies the causal Plain heap while a raw-edge Plain heap
is false. A causal heap compares Mu body/probe profiles; it does not require
all ordinary guards to be plain. Actual gate acceptance remains explicit.

`SourceCurrentActualRequiredRowOrigins` defines Root and Link. Ordinary roots
and Empty satisfy Root. Other root forms must pass the actual plain gate.
Link gives each output root row an empty effective own field or an indexed
input root row with the same complete constraint, symbol and arity, and the
same tracked child. Link is reflexive and transitive. A nonempty output own
field excludes the plain alternative and gives the indexed source origin.
Actual Required workers derive this law from initial facts. Their literal
successful equations supply their own execution graphs and reached states.

`SourceCurrentActualClassRowOrigins` composes that relation through actual
below edits, class dispatch, the tail-first right fold and Empty propagation.
Actual preparation followed by the actual class pass derives the intervening
physical state, stored memo, source index, availability and causal heap.
It does not assume a desired intermediate origin or a future invariant.

`SourceCurrentPrimaryRootSupport` connects actual false primary observations
to Root for a selected original value. The production theorem and the full
public probes record its exact selected-slot premises. This supplies a local
entry condition. It does not turn Root into a restriction satisfied by every
public input or certify arbitrary new values from earlier edits.

## Source support and remaining work

Public smart Mu permits used recursive bodies with nontrivial constraints.
The constructor does not enforce the plain gate. Existing EqualitySpec code
already uses this form. The frozen root-support review pins the definitions
and states that its Haskell expression is source-derived, not a fresh run.
This is a proof-support boundary. It is not a new production defect.

Primary selection scans original values once. Later class edits use updated
values. The new local fold preserves Root for its tracked value once Root
holds. Empty or untouched Required schedules can retain constrained Mu and
need their own identity origin law. ExposureSafe alone does not imply Root.
The general public-driver-to-selected-class support composition remains open.

Row origins currently refer to the immediate input forest. Relate recursive
Head reconstruction and native writer results to proper occurrences in the
initial source. Then exclude collisions with every active owner and bound
fresh recursive calls, or prove a well-founded measure. Key exclusion alone
does not prove termination. Inherited path height can increase.

Complete used-local binder induction and earlier-writer alignment. Prove
general recursive outer language preservation and repeated-pass convergence.
Complete concrete public Haskell adapters and runtime correspondence.
The completed finite ordinary outer domain is unchanged. No completion
percentage or time estimate follows from the component counts.

## Verification and preservation

Full Audit passes {jobs} jobs and {deps} dependency checks. Only the unchanged
ClosedCompletion unused-variable warning remains. All {modules} production and
{constructed} constructed strict logs have exactly zero bytes. All {public}
public and {constructed} constructed pairs have complete explicit signatures,
full proofs and axiom reports in {groups} groups. All eight required settings
are active. Only the three standard axioms occur. Effective memory maximum
and high are 4 GiB. Swap maximum is zero. Audit peak is {peak} MiB.

The source-built fixtures include a changed selected child beside an exact
retained Mu continuation, a nonempty Required schedule followed by two actual
classes, and a positive-own survivor whose origin uses Link.positive.
Component manifests and root checks record the selected production and
constructed probes. Every failed numbered source and raw log is retained.
Evidence is in `restart-evidence/20261018-actual-positional-lineage/`.

All 25578 starting files remain present. All 3209 older non-Audit Lean
sources, 242 Haskell files, 206 active-package files, two stashes and three
other worktrees remain unchanged. Audit only adds the declared imports.
The preservation report checks 133 frozen manifests and {967+modules} module
entries. No Haskell patch is added. Field-pool repair b9219b9e remains fixed
at main c0cc8a05. FINDINGS retains the external repair registry first.
Publication still awaits the existing direct approval. No push is attempted.
'''
p=R/'lean/notes-current-actual-positional-lineage.md';assert not p.exists();p.write_text(note)
print(json.dumps({'updated_at':now,'proof':proof,'files':9}))
