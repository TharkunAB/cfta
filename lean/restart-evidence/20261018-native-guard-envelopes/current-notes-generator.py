import datetime
import json
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
checked = json.loads((HERE / 'checkpoint-validation.json').read_text())
proof = checked['proof_commit'][:8]
now = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
entries = checked['component_entries']
section = f'''## Current initial guard envelopes and finite Parent reservations

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `9964fe28`. Main source remains `c0cc8a05`.
Read `lean/notes-current-native-guard-envelopes.md` for exact boundaries.

The finite physical guard alphabet now computes a common raw guard vector.
Actual resident prechecks derive their own class, path and step bounds.
Initial native query support constructs the actual receipt and transports
the raw vector through its literal finite alphabet extension schedule.
No hereditary ordinary domain, finite Cap or inherited-size premise is added.

The four raw limits do not bound child-index values. Current Required/Edit
forecasts include those values in sizeOf. A separate exact finite alphabet
reservation now covers the complete own Record syntax, original child counts
through the mass bound, and all ordered ambient words through the initial
edge-counter bound. Context/Fits, flat membership, inherited readiness and
residency derive the actual Parent reservation. No full Frame is needed for
this numeric transfer. No future entry-state callback or result is assumed.

A literal query on two distinct closed resident Mu operands produces a
nonempty result and actual native node and edge work. Its initial facts and
guard bounds are derived internally. The returned bounds align to the exact
literal result and full Checked state. A separate live recursive Parent
fixture derives its own finite UniformReserved and constructs the actual
body. A raw rejection fixture uses zero lower fuel and no class Room.

Full Audit passes 3237 jobs and 70923 checks. Three production and two
constructed strict logs are empty. All 12 public and 3 constructed full
pairs pass in 5 groups with all eight settings and standard axioms.
Audit peak is {checked['audit_peak_MiB']} MiB under 4 GiB maximum/high and zero swap.
Six component manifests pin {entries} entries. Evidence is in
`lean/restart-evidence/20261018-native-guard-envelopes/`.

Next compose the single-Parent resource and guard schedules across the
fixed outer fuel/phase call tree. Derive semantic Reads/Post/Frame through
rows_tail and walk_tail. Initial recursive completion, all-owner separation,
fresh-call bounds, recursive outer language preservation, used-writer
alignment, repeated convergence and public Haskell correspondence remain
open. The strongest complete ordinary outer domain is unchanged.
No Haskell patch or new production defect is added. Field-pool repair
b9219b9e remains fixed in c0cc8a05. Keep FINDINGS first. The full-library
goal stays active. Publication awaits the existing direct approval.
No push is attempted or retried.

'''
anchor = '## Current semantic context at actual Parent and outer edge returns\n'
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
             'lean/API-COVERAGE.md', 'lean/COVERAGE.md']:
    path = ROOT / name
    text = path.read_text()
    assert text.count(anchor) == 1 and section.splitlines()[0] not in text
    path.write_text(text.replace(anchor, section + anchor, 1))
path = ROOT / 'FINDINGS.md'
text = path.read_text()
registry = '## Haskell fix handoff for external work\n\n'
assert text.count(registry) == 1
entry = f'''Current proof update: {now}. Proof checkpoint is `{proof}`.
Initial physical guards now derive raw Bounds and actual own-class limits.
Native query completion carries those limits to its exact returned heap.
Exact finite own-record and ambient-word reservations also derive the actual
Parent reservation from initial Context/Fits and resident input facts.
The exact carrier retains child-index syntax omitted by the four raw limits.
No finite ordinary domain, finite Cap, inherited-size bound or future-entry
capacity callback is added. Whole bounded outer scheduling and recursive
progress remain open. Full Audit passes 3237 jobs and 70923 checks.
No Haskell patch or new production defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-native-guard-envelopes.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

'''
path.write_text(text.replace(registry, registry + entry, 1))
path = ROOT / 'lean/notes-proof-status-20261017.md'
text = path.read_text()
assert 'Checked at proof checkpoint `b82efb10`.' in text
text = text.replace('Checked at proof checkpoint `b82efb10`.',
                    'Checked at proof checkpoint `' + proof + '`.', 1)
text = text.replace('[the current checkpoint](notes-current-parent-semantic-reads.md).',
                    '[the earlier checkpoint](notes-current-parent-semantic-reads.md).', 1)
paragraph = '''The finite physical guard alphabet now derives initial flat raw bounds and
actual precheck class/path/step bounds. Initial native queries construct
their own receipts and returned guard bounds. Exact finite own-record and
ambient-word reservations retain index-sensitive compiler syntax and derive
the actual Parent reservation from current initial Context/Fits. No inherited
size, hereditary domain, finite Cap or future-entry capacity callback is
added. Single-Parent initial scheduling is checked. The general fixed-fuel
outer resource/guard composition and semantic rows_tail/walk_tail summaries
remain open. General recursive completion and the strongest complete outer
domain are unchanged. Read
[the current checkpoint](notes-current-native-guard-envelopes.md).

'''
anchor = '## Strongest current claim in plain technical English\n'
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, paragraph + anchor, 1))
note = f'''# Initial guard envelopes and finite Parent reservations

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `9964fe28`. Main source: `c0cc8a05`.
This is verified progress. The full-library goal remains active.

## Strongest complete statement

Validated finite explicit graphs, including cycles, have exact distinct-term
size classes, counts, specified ordering and rank/unrank inverses in the
checked implementation model. Correct finite yes/no guard replies and the
ordering laws remain explicit. Unknown replies can return an error.
Supported closed resident Original operands have exact recursive native
intersection semantics. Initial resource bounds construct their executions.
The complete finite ordinary constrained outer pass preserves the full
guarded language. Its domain excludes Mu, references and explicit unions
in every descendant. General recursive outer completion and complete public
Haskell correspondence remain open. Read `notes-proof-status-20261017.md`.

## Computed physical raw bounds

GuardHeapBounds.limits joins the computed raw vector of each actual initial
guard. alphabet proves every literal member satisfies that vector. initial
uses coherent physical edge records to establish the same bound at every
stored edge key. It imposes no hereditary shape restriction on values.
resident_complete constructs its own actual allocated precheck. Every live
own class list then has derived class count, path count, path depth and total
class-step bounds. The inherited payload needs readiness, with no size bound.

NativeGuardEnvelope.advance follows the literal NativeGuardAlphabet.step
schedule. The alphabet proof includes retained guards, Top and every source
conjunction. complete invokes the initial numeric native query producer and
derives flat raw guard Bounds at the same returned heap. Its own receipt
retains actual physical execution, semantic laws, Frame/Fits and resources.
No future trace, returned guard law or finite input Cap is supplied.

## Exact single-Parent reservation

Stored value mass ignores guards. The raw four-component vector bounds
occurrence counts, depths and guard stages. It does not bound path-index
magnitudes. Current Required/Edit forecasts use sizeOf on complete compiled
syntax, including those magnitudes and retained callback paths.

ParentAlphabetReservation retains the complete finite alphabet instead.
ownRecordImage evaluates each literal own accessor and keeps its exact
ordered Record list. wordsThrough enumerates every ordered ambient guard
word through the initial edge-counter bound. Duplicates remain included.
UniformReserved checks pure ClassesForecast reservations for that finite
image, child counts from zero through profile.mass, and those ambient words.
It quantifies over no future caller state, result or successful execution.

resident_reserved derives the literal ParentForecast.residentReserved.
Initial Context, Profile/Fits, flat alphabet membership, inherited readiness
and resident row supply its actual field and own precheck. Exact readback
identifies its record image. The stored edge payload bounds child count.
Successful physical edge reads bound the ambient alphabet length. Complete
index and callback syntax therefore remains present in the forecast.
The transfer needs no full Frame. Later semantic execution still needs one.
The raw rejection branch itself performs no live reservation work.

## Constructed scope

One source-built query uses two distinct actual recursive Mu operands.
Both are closed and resident. Its literal native execute128 returns a
nonempty value with more than one native node cell and at least one native
edge cell. Initial inventory, Frame/Fits and Room128 are derived internally
at width130. Computed initial guard bounds and the new complete producer
align to that exact literal result and complete Checked state by successful
return uniqueness. This is actual native work with derived returned bounds.
It establishes no host64 capacity claim or public Haskell execution.

A separate source-built resident Parent fixture has live own paths [0] and
[1] over two constrained recursive children outside every finite Plain Cap.
It derives a finite joined-profile Room and its own UniformReserved, then
consumes resident_reserved and constructs the actual EdgeBody return.
It is numeric completion and replay. The separate raw rejection fixture
checks zero lower fuel and omits class Room. Read the frozen component
reviews for their exact statements and all preserved attempts.

## Remaining work

The full fixed-fuel outer schedule is still open. Each rows or walk cons
decreases outer fuel. Same-fuel control changes have a finite phase order.
A conservative call-tree bound can therefore be derived from the supplied
outer fuel without a retained source-height measure. Compose the current
single-Parent resource and guard forecasts across that bound. Then derive
actual Walk/Rows semantic reads, Post, full Frame and updated Fits through
completed earlier ordinary nodes. Do not replace these producers with a
capacity callback at every future entry.

This bounded task does not exclude all active owners or prove a sufficient
outer fuel. General recursive progress, fresh-call bounds, recursive outer
language preservation, used-writer alignment, repeated convergence and
concrete Haskell/runtime correspondence remain open. The strongest complete
ordinary outer domain is unchanged.

## Verification and preservation

Full Audit passes 3237 jobs and 70923 dependency checks. Only the unchanged
ClosedCompletion warning remains. Three production and two constructed
strict logs are zero bytes. All 12 public and 3 constructed full pairs pass
in 5 groups with all eight settings and standard axioms. Effective memory
maximum/high limits are 4 GiB. Swap maximum is zero. Audit peak is
{checked['audit_peak_MiB']} MiB. Six component manifests pin {entries} entries.
Evidence is in `restart-evidence/20261018-native-guard-envelopes/`.

All 26994 starting files remain present. All 3233 older non-Audit Lean sources,
242 Haskell files and 206 active-package files retain their bytes. Two stashes
and three other worktrees retain their metadata. Audit only adds three
imports. The preservation report checks 141 frozen manifests and 994 module
entries. Root FINDINGS retains every earlier repair entry. No Haskell patch
or new production defect is added. Field-pool repair b9219b9e remains fixed
in c0cc8a05. Publication awaits the existing direct approval. No push is
attempted. The full-library goal remains active.
'''
path = ROOT / 'lean/notes-current-native-guard-envelopes.md'
assert not path.exists()
path.write_text(note)
print(json.dumps({'proof': proof, 'updated': now}))
