import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-pair.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
counts = json.loads((HERE / 'attempt-expectations.json').read_text())
source = ROOT / 'lean/MicroCFTA/SourceCurrentActualOwnerPair.lean'
digest = hashlib.sha256(source.read_bytes()).hexdigest()
assert digest == '3e10a892e36f1e5f981fc0acf60c86af543ad3e91bf46ce79205aad365c7a930'
audit = (HERE / 'audit-1.log').read_text()
assert f"Build completed successfully ({counts['audit_jobs']} jobs)" in audit
assert f"{counts['audit_dependencies']} MicroCFTA theorems" in audit
assert not (HERE / 'pair-strict-1.log').read_bytes()
evidence = (f"Audit passes {counts['audit_jobs']} jobs /{counts['audit_dependencies']} dependencies. "
    f"Five actual Lean/Lake commands include one retained strict failure.")
update = f'''## Current same-owner pair in the actual combined equality classes

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-actual-owner-pair.md`.

ActualOwnerPair.required_pair now derives two distinct suffixes through
the SAME child in one class of the actual combined inherited constraint.
The original owner row, original child forest, selected precheck/Scan,
Required return, pass output and positive ancestry remain correlated.
Nonempty retained records derive that SAME member row is nonplain.
No nonplain, backwards relation or common-anchor oracle is supplied.

The actual inherited-first prefix supplies one live combined payload.
Its genuine operation validity, inherited readiness and available field
derive fixedness and whole-class Covers. Both endpoints of each old class
relation enter one covering component with the SAME suffix. Individual
path membership is insufficient. RequiredPositiveChronology.pass runs
once; PositiveOwnerPair then uses the exact original row.children lookup.
No finite enumeration or runtime rank is a caller premise.

The theorem consumes actual Precheck/Retained/Required/PassReads
certificates and genuine historical native, Merge and global memo laws.
It does not yet derive those certificates from the literal Parent worker
or store the laws in a cold/warm writer ledger. The live combined-payload
branch is explicit. Contradiction and delayed descent remain separate.

Root strict, complete FULL and independent review pass. {evidence}
The source-only reserved binder was renamed before the first proof job.
The failed strict found projection notation and Except type inference.
The final mechanical fix changes no mathematical premise or conclusion.
Selected checks are clean. FULL uses all eight settings, identical public
types and standard axioms. No canonical, infrastructure or constructed job.
Only the old ClosedCompletion Audit warning remains. Counts do not measure
completion. A separate pinned erratum corrects a usage-report sentence;
raw samples are 52, 52 and 51 percent. All passed the fresh usage gate.

The next local plan obtains exact selected Required/pass certificates
from ONE numeric Parent receipt. Existing record-worker completion and
full-result uniqueness retain complete records, trie fields and order.
Path projection need not be injective. Historical native entry production,
unfinished prefix resources, actual owner exclusion, renewal, retention,
outer completion, convergence and Haskell refinement remain open.

All older sources, evidence and controlled version exceptions remain.
Haskell/packages/main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its repair index FIRST.
The full goal stays active.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
ActualOwnerPair.required_pair now connects actual Required/pass positive
ancestry to two distinct suffixes through one child in the SAME actual
combined class. Nonempty retained/precheck records derive the original
row is nonplain. Actual inherited-first allocation derives whole-class
Covers and fixedness. Both endpoints and their same suffix enter one
covering component. No desired backwards relation, common anchor, caller
enumeration or runtime rank is supplied.

Actual execution certificates and historical native/Merge/global memo
laws remain genuine premises. Exact Parent-to-certificate production and
cold/warm writer retention remain open, along with unfinished prefixes,
owner exclusion, renewal, retention, outer completion, convergence and
Haskell refinement. The result covers a live combined payload.

Root strict empty; full public readback and independent review pass.
{evidence}
The failed elaboration and all prelaunch source versions remain.
A pinned metadata erratum records actual usage samples 52/52/51 percent.
No Haskell source, runtime result, external repair or imported main changes.
Read `lean/notes-current-actual-owner-pair.md`. Goal active.
The external Haskell repair index stays FIRST.
'''
note = f'''# A same-owner pair in the actual combined family

Updated: {now}. Selected proof: `{proof}`.
SourceCurrentActualOwnerPair has 189 lines and one public required_pair.
Selected source SHA256: {digest}.

The theorem consumes one Precheck receipt for the original owner member
row, one admitted Scan with its exact Retained record certificate, one
Required receipt, and the exact completed class PassReads. The result
owner occurs at the same output index. The source forest is the SAME
original row.children, including the exact original positive suffix.

Precheck.classes gives the original own records and their ordered form.
Retained.fields gives the exact kept Sublist. Nonempty kept records imply
the original effective own classes are nonempty. SourceMemoGate.plain
therefore returns false for that same member row. PositiveAt.root can
then supply the owner root without historical owner availability.

The supplied outer inherited-first prefix is a real operation equation.
Its initial Valid, inherited Ready and FieldAvailable facts construct
the own accessor. combine_covers derives a fixed combined payload and
whole-class Covers. The actual function equation identifies the SAME
combined value. The proof maps each retained record through ordered_perm
to the original sourceEqualities and into that actual combined family.

The private Rel lift recurses on reflexive, member and transitive cases.
The member case selects ONE covering component. Both original class
members enter that component with the SAME appended suffix. It does not
substitute independent memberships after classes merge.

RequiredPositiveChronology.pass runs once on the exact Required receipt
and class reads. The real scanned Current, positive native Support and
causal History remain inputs, as do semantic/cost/UnionNormal/availability,
original false primary gates, physical Merge Stored, semantic CacheCovers,
prepared global memo Valid, conditional Merge Stored and positive Merge
Support. It returns positive ancestry in the SAME original row.children.
The proof lifts only Rel through Covers. It preserves the lookup and path.

PositiveOwnerPair.same_child_pair runs once for that actual member row,
derived nonplain fact and same combined fixed family. The finite positive
path argument produces one combined class containing index::left and
index::right with left different from right. The caller supplies no
finite enumeration, backwards relation, common-anchor witness or count.
This is path geometry. It is not an execution or unfolding rank.

The public conclusion retains nonplain, Covers, fixedness and the pair.
It covers combined.payload = some outputs. The contradiction branch of
outer allocation is separate. DelayedCombinedOwnerProgress.key_ne_top
can consume the pair together with real later validity/growth and an
initially Ready Top owner; that additional consumer is not proved here.

Root read every original 188 source line and all later deltas. Independent
review found the reserved prefix binder before launch. Its two-line
alpha-renaming is preserved beside the unexecuted original snapshot.
The first actual strict command failed on Record.paths notation and one
ambiguous Except constructor. The final source qualifies the projections
and annotates that existing equality. No mathematical premise, conclusion,
execution witness or proof route changed. The frozen proposal stays
unchanged; type comparison records the binder/projection normalization.

Selected and root strict logs are empty. Complete FULL has 409548 bytes,
SHA256 f646fd885f0e78ae44ab86db394e1738d690a8c77a6215029ac48ef177d1958c.
It prints the complete public proof and type with all eight settings,
identical checked and printed types, no private public predicate and no
omission. Actual dependencies are propext, Classical.choice and Quot.sound.
{evidence}
Three author commands include one failed strict; root adds strict and
default Audit. No reviewer proof, canonical, infrastructure or constructed
job ran. Copies add no jobs. All commands retain fresh usage, effective
max/high 4 GiB, zero swap and five-minute limits. Only the old Audit warning
remains. The frozen author report incorrectly says all samples are52.
Its separate pinned erratum gives the actual strict1/strict2/FULL samples
as 52/52/51. All exceeded the threshold. No proof evidence was changed.

This local theorem uses admitted execution certificates. It does not
derive them from bare worker success. The next local producer should use
ONE numeric Parent receipt and its exact actual reads. Record-worker
completion and full-record uniqueness already identify exact kept fields
without path-map injectivity. Required and class reader admission must
come from genuine entry resources, not a supplied reached Ranges oracle.

The same historical writer must retain its own initial native laws and
resources. Current reader facts cannot supply them. Cold/warm retention,
unfinished prefixes, actual owner exclusion, renewal, unfolding progress,
final retention, outer completion, convergence and Haskell refinement
remain open. Earlier proofs, counterexamples and version exceptions stay.
Haskell/packages/main remain unchanged. No new Haskell runtime defect or
external repair. FINDINGS keeps its repair index first. Goal active.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        prefix = '# Current formalization findings\n\n## Haskell fix handoff for external work\n'
        marker = prefix + '\n' + (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker)
        rest = original[len(marker):]
        assert rest.startswith('\n')
        changed = marker + '\n' + findings + '\n' + rest[1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
(ROOT / 'lean/notes-current-actual-owner-pair.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
