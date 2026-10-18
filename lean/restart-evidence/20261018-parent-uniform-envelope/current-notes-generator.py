import datetime
import json
from pathlib import Path
from zoneinfo import ZoneInfo
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
checked=json.loads((HERE/'checkpoint-validation.json').read_text())
proof=checked['proof_commit'][:8]
now=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
body=(HERE/'current-body.txt').read_text()
validation=f"""Full Audit passes {checked['audit_jobs']} jobs and {checked['audit_dependency_checks']} checks.
Four production and three constructed strict logs are empty. All
{checked['new_public_pairs']} public and {checked['constructed_pairs']} constructed full pairs pass in {checked['groups']} groups.
All eight settings and standard axioms pass. Audit peak is
{checked['audit_peak_MiB']} MiB under 4 GiB maximum/high and zero swap.
Six component manifests pin {checked['component_entries']} entries. Evidence is in
`lean/restart-evidence/20261018-parent-uniform-envelope/`.
"""
remaining="""General recursive outer progress, all-owner separation, fresh-call bounds,
recursive language preservation, used-writer alignment, repeated convergence
and public Haskell correspondence remain open. The strongest complete
ordinary outer domain is unchanged. No Haskell patch or new production
defect is added. Field-pool repair b9219b9e remains fixed in c0cc8a05.
Keep FINDINGS first. The full-library goal stays active. Publication awaits
the existing direct approval. No push is attempted or retried.
"""
section=f"""## Current finite Parent envelopes and outer Parent call budgets

Updated: {now}. Proof checkpoint is `{proof}`.
Starting local checkpoint is `b05e4891`. Main source remains `c0cc8a05`.
Read `lean/notes-current-parent-uniform-envelope.md` for exact boundaries.

{body}
{validation}
{remaining}
"""
anchor='## Current initial guard envelopes and finite Parent reservations\n'
for name in ['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md']:
 path=ROOT/name
 text=path.read_text()
 assert text.count(anchor)==1 and section.splitlines()[0] not in text
 path.write_text(text.replace(anchor,section+anchor,1))
path=ROOT/'FINDINGS.md'
text=path.read_text()
registry='## Haskell fix handoff for external work\n\n'
assert text.count(registry)==1
entry=f"""Current proof update: {now}. Proof checkpoint is `{proof}`.
Finite initial cases now bound Parent output profiles and all nine fuels.
A joined initial Room test derives its complete reservation. A computed
mathematical width supplies Room, without a host64 capacity claim.
Actual Target completion also constructs its finite guard carrier. The
literal bounded outer replay retains entered Parent callers and bounds
their count from supplied outer fuel on every outcome. It excludes other
outer allocations. Full Parent carrier and outer scheduling remain open.
Full Audit passes {checked['audit_jobs']} jobs and {checked['audit_dependency_checks']} checks.
No Haskell patch or new production defect is added. Field-pool repair
`b9219b9e` remains fixed in `c0cc8a05`. Read
`lean/notes-current-parent-uniform-envelope.md`. Keep this registry first.
Record each later repair with failure, executable reproducer, paths, commit,
checks and upstream status. Preserve every earlier repair entry below.

"""
path.write_text(text.replace(registry,registry+entry,1))
path=ROOT/'lean/notes-proof-status-20261017.md'
text=path.read_text()
assert 'Checked at proof checkpoint `1f9c135c`.' in text
text=text.replace('Checked at proof checkpoint `1f9c135c`.','Checked at proof checkpoint `'+proof+'`.',1)
text=text.replace('[the current checkpoint](notes-current-native-guard-envelopes.md).','[the earlier checkpoint](notes-current-native-guard-envelopes.md).',1)
paragraph="""Initial exact finite cases now bound the complete Parent output profile
and all nine lower fuels. One joined Room test derives UniformReserved;
a computed mathematical width supplies that test. This asserts no host64
capacity. Actual Target completion constructs a finite returned guard
carrier. A separate literal outer replay bounds entered Parent calls from
supplied outer fuel on every outcome. Other outer allocations remain outside
that count. Full Parent carrier, outer resource scheduling and semantic
rows_tail/walk_tail composition remain open. General recursive completion
and the strongest complete outer domain are unchanged. Read
[the current checkpoint](notes-current-parent-uniform-envelope.md).

"""
anchor='## Strongest current claim in plain technical English\n'
assert text.count(anchor)==1
path.write_text(text.replace(anchor,paragraph+anchor,1))
note=f"""# Finite Parent envelopes and bounded outer Parent calls

Updated {now}. Proof checkpoint: `{proof}`.
Starting local checkpoint: `b05e4891`. Main source: `c0cc8a05`.
This is verified progress. The full-library goal remains active.
Read [the overall proof status](notes-proof-status-20261017.md).
The strongest complete ordinary outer domain is unchanged.

{body}
## Exact boundaries

ParentUniformEnvelope.classesProfile joins each exact own-record image,
original child count through initial mass, and ordered ambient guard word
through the initial edge bound. Full path-index and callback syntax remains
present. profile adds one constructor at the maximum original child count.
fuel takes the finite maximum of the corresponding class fuel forecasts.
resident_bounds derives both bounds from initial Context/Fits, flat guard
membership, inherited readiness and resident input. It needs no full Frame.
complete also takes Frame and UniformReserved. It constructs the complete
Parent receipt, common returned Fits and replay for independently larger
values of all nine lower fuels.

ParentInitialRoom.scan_reserved_of_room derives every predicted Scan query
reservation from its final pure profile. classes_reserved_of_room includes
preparation and the class fold. uniform_of_room applies that result to each
finite initial case. roomBits and room_computed give one sufficient natural
width for any finite profile. uniform_computed combines these facts.
The finite profile and guard functions are proof forecasts. There is no
claim that the Haskell API computes or can store these large forecasts.
The constructed Parent derives its initial source, semantic context, Frame,
Fits and reservation. Its own paths [0] and [1] use constrained recursive
children outside every finite Plain Cap. The checked endpoint is numeric
completion and replay at the common ceiling. It does not assert a separate
small-fuel observation or a specific positive returned constructor.

TargetGuardAlphabet follows the actual Operand, tail and query order.
Each Operand adds at most Top. Each native query contributes its predicted
instruction count at the predicted query entry. The returned full Target
graph, Reads, semantic receipt, Frame, Fits and computed worker equation
share the same result and complete Checked state as the guard carrier.
Initial selected-path closure, semantic cache laws and pure reservation
remain explicit. The constructed Target derives its own source and Room.
It uses repeated paths and keeps an unrelated open sibling outside selected
path closure. This result does not yet extend through shared edits, class
folds, Scan and complete Parent construction.

OuterCallBudget instruments all eight literal outer phases. Its bind enters
only actual successful continuations and retains every failed prefix. A
warm hit adds no Parent call. A cold Parent body adds its stored owner
request and the complete body-entry caller, including failures. Erasure
equals the literal complete outcome. The budget uses supplied outer fuel
and finite phase order, independent of source height, Ready, Room or a
completed graph premise. The constructed checks cover multiple entered
rows, an exhausted prefix and a zero-fuel warm hit. Mu reconstruction, raw
rebuild, inherited descent and lower instructions are outside this count.

## Next proof target

Extend the Target carrier through whole shared edits, class right folds,
Scan, Required and Parent. Keep the common Profile and complete guard
alphabet linked at the same actual return. Add the separate numeric and
guard costs for outer reconstruction and descent. Then compose these
uniform steps along the bounded outer replay. Derive semantic Reads, Post,
Frame and Fits across rows_tail and walk_tail. Do not replace initial
producers with a future-entry capacity or semantic callback.

A fixed-fuel count does not establish sufficient outer fuel. General
recursive progress still needs all-active-owner separation and a bound
on fresh calls or another well-founded measure. Used-binder and earlier
writer alignment, recursive outer language preservation, repeated-pass
convergence and public Haskell correspondence remain open.

## Verification and preservation

{validation}
All 27143 starting files remain present. All 3236 older non-Audit Lean
sources, 242 Haskell files and 206 active-package files retain their bytes.
Two stashes and three other worktrees retain their metadata. Audit only
adds four imports. Preservation checks 142 frozen manifests and 998 module
entries. Every earlier FINDINGS repair entry remains present.

{remaining}"""
path=ROOT/'lean/notes-current-parent-uniform-envelope.md'
assert not path.exists()
path.write_text(note)
print(json.dumps({'proof':proof,'updated':now}))
