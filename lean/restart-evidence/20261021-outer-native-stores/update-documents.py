import datetime
import hashlib
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-outer.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
source = ROOT / 'lean/MicroCFTA/SourceCurrentOuterNativeStores.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == 'b9f7f87df92990b460708bd71fb5f56085bc3b28b97c0a0d96ae1e12f6156f46'
assert not (HERE / 'outer-strict-1.log').read_bytes()
audit = (HERE / 'audit-1.log').read_text()
assert 'Build completed successfully (3596 jobs)' in audit and '74948 MicroCFTA theorems' in audit
update = f'''## Current native stores through completed recursive outer calls

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-native-stores.md`.

OuterNativeStores.edge_call keeps one supplied numeric edge receipt and
adds positive native Support, causal Mu History, conditional Merge Stored
Plain, positive Merge Support and UnionNormal at its exact returned caller.
node_call and descendants preserve these laws through all six internal
recursive phases. The proof follows actual completed earlier siblings.
Existing public producers supply their Post, Frame, updated Fits, Carrier
and exact global memo bundles. No old inventory or profile is reused after
real allocation. The new laws depend on the same returned caller; separate
existential global bundles need not be equated.

Cold edge calls use the same captured owner and actual Parent graph.
Ready hits keep the caller. Actual raw edge/node reconstruction supplies
Extension and unchanged native cells for SupportAdvance. Actual NoNewMu
supplies causal History.retain. Resident Mu cleanup keeps the entire caller
under the existing probe invariant. No unrestricted Mu ancestry law is added.

Genuine entry Context/Frame/Fits, finite guard Carrier, scheduled Room,
phase inputs, normality and initial store laws remain. A successful return
does not create these premises. The result proves preservation, not general
termination. Existing OuterInitialPrefix.reached already supplies ordinary
resources at unfinished prefixes without a future enclosing return. Adding
the new store laws there and integrating the same-writer resource ledger
remain next. Owner exclusion, renewal, final retention, outer completion,
convergence, broader initial resources and Haskell refinement remain open.

Root strict, complete FULL and independent review pass. Audit passes
3596 jobs /74948 dependencies. Seven actual Lean/Lake commands include
three retained failed stricts; the second includes warnings. Selected and
root strict logs are empty. All three public heads have complete identical
checked/printed types, all eight settings and standard axioms. No canonical,
infrastructure or constructed job. Only the old Audit warning remains.
Counts do not measure completion. Prelaunch and failed source versions stay.

All old sources/evidence and version exceptions remain. Haskell/packages/
main, stashes and other worktrees stay unchanged. No new Haskell defect or
repair. FINDINGS keeps the external repair index FIRST. Goal active.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
Native Support, causal History, conditional Merge Stored Plain, positive
Merge Support and normality now survive completed recursive outer calls.
The three public heads are edge_call, node_call and descendants. Six private
phase cases retain the actual return states and scheduled resource order.
Genuine initial semantic/numeric, Carrier/Room and positive-store contracts
remain. No future return, caller ancestry or arbitrary Mu law is supplied.

Strict/FULL/independent review pass; Audit 3596 jobs /74948 dependencies.
Seven actual commands retain three failed stricts, including strict2 warnings.
Selected checks are clean. No canonical, infrastructure or constructed job.
The new unfinished-prefix store extension and correlated historical writer
ledger remain, then owner exclusion, renewal, retention, completion,
convergence and Haskell refinement. Counts do not measure completion.
No Haskell source, runtime result, imported main or external repair changes.
Read `lean/notes-current-outer-native-stores.md`. Goal active.
The external Haskell repair index stays FIRST.
'''
note = f'''# Native stores through completed recursive outer calls

Updated: {now}. Proof: `{proof}`.
SourceCurrentOuterNativeStores has 528 lines and three public theorems:
edge_call, node_call and descendants. Selected SHA256:
b9f7f87df92990b460708bd71fb5f56085bc3b28b97c0a0d96ae1e12f6156f46.

The four new laws are positive native Support, actual causal Mu History
from empty, conditional Merge Stored Plain and positive Merge Support.
The endpoints also retain UnionNormal. Initial Context, Frame, numeric
Fits, phase input readiness/residency, finite guard Carrier and computed
scheduled Room remain genuine requirements. Initial normality and the four
store laws remain explicit. Current derives from Frame. None follows from
raw worker success alone.

edge_call consumes one fixed EdgeCallNumeric receipt. A ready hit retains
the entire caller. A cold evaluation retains that receipt's captured owner,
real beginEdge event and actual Parent graph. Graph completion supplies the
literal Parent return at sufficient lower fuels. GeneralParent preserves
the four laws there. Finishing changes only the outer result cell. The old
supplied edge receipt and its global bundle stay fixed. The new Parent
producer's independent existential bundles are not equated with them.

node_call and descendants use a private strong-fuel induction with six
phases: node call, node body, rows, descendants, children and indexed walk.
Each completed head is the exact earlier worker call. Existing public
OuterInitialActual endpoints supply its actual Post/Frame/Fits/Carrier and
global memo bundle. The new store properties depend only on that same
returned caller. They combine with its old resource receipt without a
claim that two independent existential memo bundles are identical.

Rows use the actual edge call, actual descendants and actual row suffix.
The seed advances through parent then descendants. Indexed walks use the
actual inherited descent, actual node call and actual next slot. The next
seed is the completed head's node schedule. Each subcall Room follows the
existing schedule inequalities. No per-sibling Ready or future-return oracle
is introduced, and no old inventory or Fits is copied across real work.

Inherited prefix and equality descent retain native state and Merge.
Raw edge and node reconstruction use their actual constructor receipts.
SupportAdvance takes real Extension, final Good and unchanged native cells.
History.retain instead takes actual NoNewMu: edge work retains nodeRecords,
and changed node work uses makeNode_noNewMu. An unchanged modification is
literal identity. Growth alone is not a causal history. Resident Mu cleanup
retains the whole caller under Context.probes and residency. It needs no
unrestricted opaque-Mu positive-output law. Both Merge laws follow the same
literal Parent and constructor order.

Root and independent review read the complete original 521-line source and
every repair delta. A prelaunch one-line beta reduction preserves the old
unexecuted source. Three actual strict failures remain. They expose implicit
branch names, completed-state/request inference, native advance unfolding,
phase-bundle type inference and the local captured-request let in a simp
rule. Strict2 also reports redundant-instance warnings. The repairs retain
the same captured request, clauses, resources and public statements. The
private reservation helper now has only its needed EdgeDec instance.
The final three public headers are text-identical to the frozen proposal.

Selected strict4 and root strict logs are empty. Complete FULL has 188492
bytes and SHA256 d999ea714584b13639dd1119849f818dbc05f0d7bee82873219d2fb9cf026606.
All three heads have all eight settings, full proofs, exact checked/printed
type identity, no private public-type predicate and no omissions. Each uses
only propext, Classical.choice and Quot.sound. The selected source passed
without further changes. Five author commands plus root strict and Audit
give seven actual Lean/Lake jobs, three failed. No reviewer proof, canonical,
infrastructure or constructed job ran. Each actual job retains fresh usage,
effective max/high 4 GiB, zero swap and a five-minute cap. Audit passes 3596
jobs /74948 dependencies with only the old ClosedCompletion warning.

Existing OuterInitialPrefix.reached already supplies same-prefix SeedTrace,
Post/Frame/Fits/Carrier/Inputs and scheduled Room without a future outer
return. A new store-only prefix induction can now use these three completed
endpoints at rows_edge, rows_tail and walk_tail. That extension remains.
The frozen next local writer plan retains ONE complete writer caller,
global memo bundle, inventory, profile, literal Parent execution and all
entry resource/store facts inside one existential. Public generic memo
lifecycle helpers avoid copying the old 551-line ledger. A warm reader
must recover that stored witness. It cannot infer old entry facts from
current growth. The local ledger and its integration remain unproved here.

The broad semantic claim stays conditional: supported successful model
traversal with empty inherited constraints preserves exactly the accepted
finite terms. The whole-library target requires termination and each public
Haskell specification from valid supported INITIAL inputs. This checkpoint
does not remove success as a premise. Owner exclusion, renewal, fresh-call
bounds, final retention, outer completion, repeated-pass convergence,
broader initial-resource production and Haskell refinement remain open.
All old proofs, counterexamples, logs and version exceptions stay. Haskell/
packages/main remain unchanged. FINDINGS keeps its repair index first.
The full goal stays active.
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
(ROOT / 'lean/notes-current-outer-native-stores.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
