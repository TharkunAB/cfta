import hashlib
import json
from pathlib import Path

area = Path('/tmp/mcfta-native-selected-step-20261026')
public = (area/'public-final-2/raw.log').read_bytes()
block = '''## One selected worker joins recursion, narrowing and ordinary expansion

Narrow adapter: `01a2f779f`. Continuation fold: `80968dad4`.
Selected worker: `38a2df471`. Receipt posts: `549061e9f`.
The goal stays ACTIVE.

One actual worker now reads and checks once. Repeated recursion rebuilds
indexes and restarts. A false guard runs actual narrowing, its pending-slot
action, the concrete Right callback and the ordinary dispatcher. Empty
retains its actual native effects and rejects before Right. Errors and
terminal/nonordinary observations remain explicit.

The completion theorem consumes one original selected-ordinary producer.
It derives sufficient prefix and index fuel. Under the existing ordinary
shape, edge-membership and reached numeric-range conditions, it derives
adequate ordinary bounds for the SAME full worker and prefix observations.
Each receipt retains its own native Post, pending history, fragment history
and concrete Left callback capability. No future cache or success is assumed.

A separate continuation fold executes the supplied hook before the next
sibling and threads its returned native endpoint. The captured enumeration
input stays fixed. An identity hook gives exactly the old fold's result.
This hook is not yet the concrete callback and recursive driver.
All five changed modules pass strict checks. Public readback and Audit pass;
Audit checks 76960 dependencies. H6 remains the strongest end-to-end language
theorem. Next: wire actual callbacks and recursive selected steps into that
fold. Initial-only capacity, native Graph correspondence, terminal fallback,
extraction and whole-driver language semantics remain open.
Details: `lean/notes-current-pruning-enumeration-selected-step.md`.

'''
findings = '''### Combined selected steps retain actual native effects

The selected-step model now runs one actual read/check prefix and its
selected continuation. The repeated branch derives its indexed restart.
The false branch runs narrowing once and retains its returned native heap,
including on failure or Empty. Empty has raw rejection and no Right callback.
Nonempty admitted results retain safe indexed storage and the concrete
Right callback's exact pure result. Ordinary completion retains its actual
shape, nonterminal, edge-membership and reached numeric-range conditions.

The same full worker has derived adequate ordinary bounds. Every processed
receipt retains native Post from the original caller, saved query state,
pending history, fragment history and concrete Left callback capability.
No successful future action, adapter or continuation is an input premise.

The separate continuation fold passes a hook's actual returned native
endpoint to the sibling. It restores the same captured enumeration input.
Missing endpoints and explicit hook stops stay distinct. Its identity hook
reproduces the complete old fold result. The concrete callback and recursive
hook are not wired yet. Full source interleaving remains open.
No new Haskell runtime defect or repair is identified. External action:
no new patch is proposed. Keep the repair table and pending Sized repair.
Details: lean/notes-current-pruning-enumeration-selected-step.md.

'''
note = (area/'notes-draft.md').read_text()
note = note.replace('Draft. Verification and the final selected producer remain TODO.', '''Narrow adapter: `01a2f779f`. Continuation fold: `80968dad4`.
Selected worker and completion: `38a2df471`.
Per-receipt native posts and pending history: `549061e9f`.
The formalization goal stays ACTIVE. Origin/main remains
`153e1a211b56dd78bd22f6b427fb78e673041d55` after the initial pull.''')
old = '''The Right callback runs at the attached core. The runtime retains its raw
result, including pruning and errors. Only a successful singleton with a
false pruning flag enters `NativeOrdinary.run`. It frames the actual callback
core with the attached indexes. The callback raw result retains its updated
metadata. The current ordinary scanner does not yet consume a recursive
continuation hook.'''
new = '''The Right callback runs at the attached core. The concrete recordTypes_inr
theorem gives its exact pure result: false and the same metadata, at the
same core, for every callback fuel. The runtime retains this singleton row.
It frames the actual callback core with the attached indexes and then runs
NativeOrdinary. The current ordinary scanner does not yet consume a recursive
continuation hook. Terminal and nonordinary outer parents retain the actual
entry raw result with no shallow ordinary scan.'''
assert old in note
note = note.replace(old,new)
start = note.index('TODO — Final selected producer:')
end = note.index('Haskell source and H6 remain unchanged.')
note = note[:start] + '''## The original selection derives the complete selected worker

prepared_action identifies the actual nonempty preparation action. Equal
handles use pure unit. Changed handles use the actual representative read
and pending write. prepared_singleton inverts an actual success and derives
the exact singleton raw result at that same fuel and final core. It uses
representative_exact and the actual write shape. It assumes no Safe cache
or general future determinism law. This closes the raw observation needed
by the executable worker's singleton match.

run_parked, run_empty and run_narrowed state exact equations for the whole
selected worker from its actual earlier observations. They do not call a
second read/check producer. run_narrowed executes the concrete Right callback
and retains the exact NativeOrdinary observation at the reached Caller/cache.

complete starts from Context, Safe, global pending history, original pure
selection, realized native handles, representative roots, canonical counts
and candidate flags. It calls SelectedOrdinary.complete_with_history once.
The same witnesses supply both repeated and false-check branches.
No successful future action, cache adapter or continuation is an input.

The theorem derives read, check, native, representative and index bounds.
Every larger read, check and index bound gives Valid for the full worker.
Callback fuel and the five ordinary bounds stay arbitrary in this first
observation. Thus Valid does not assert that arbitrary ordinary bounds finish.
The native narrowing and representative bounds are the chosen witness bounds;
the theorem does not quantify larger values for those two bounds.

Valid exposes exact read/check receipts. The parked branch has Safe,
CacheValid at the unchanged Caller, pending history, the same counter,
preserved dependency levels and its actual restart observation. The narrowed
branch retains actual prepare equality, reached native Caller, original-to-
reached Post and unchanged query memos. Empty retains raw[] and no later stage.
Nonempty results retain Safe, CacheValid, Pending, Ready, the stored pending
handle, unchanged waiting counts and the exact Right and ordinary observations.

The ordinary capability requires an actual node, a nonterminal suspended
bucket, selected-edge membership and Ranges at the reached Caller/cache.
It derives finite ordinary bounds for the SAME FULL selected-step worker.
Only ordinary bounds change in that equation. All prefix fuels, checked core,
prepare result, reached native state, action, cache and Right rows stay fixed.
Every larger ordinary bound produces that same entered cache and scan result.

The packet retains the final Post and saved queries. Each processed receipt
retains Admitted, pending references, its actual native advance endpoint,
Post from the original Caller, saved query state, fragment history and
concrete Left callback capability. An unsupported annotation retains the
first unhandled receipt. Supported annotations give the complete scan result.
These callback capabilities remain per-receipt availability. They do not
execute callbacks between the current scanner's native alternatives.

## Verification and evidence

All five changed modules pass Lean 4.34.1 strict checking with every linter
and warnings as errors. Thirteen strict attempts retain six failures and
all actual source copies. The adapter repairs reduce both Option count binds
and use current conditional lemmas. The continuation repairs remove unused
simp arguments and explicitly reduce the known endpoint match. The completion
repairs use current conditional lemmas and place required DecidableEq
instances after the generic action helpers. No linter is disabled.

Five installed helper/consumer builds pass. Aggregate Audit passes with
3774 jobs and 76960 theorem dependencies. The checker body remains exact;
Audit adds two imports. The existing unused inputs warning is unchanged.
The dependency count is an audit count, not a completion estimate.
The final receipt-output strengthening requires a focused completion check,
installation, public readback and Audit rebuild. Earlier passing artifacts
remain in the evidence. All 22 checks run serially under 4 GiB caps.

Installed public readback checks 25 declarations and axiom sets. It prints
full Valid, selected runtime and continuation runtime definitions. The final
output has PUBLIC_LINES lines and PUBLIC_BYTES bytes, with no ellipsis.
SHA-256: PUBLIC_SHA.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The earlier public output remains separate. No project or native-evaluation
axiom is added. Independent source reviews check original inputs, actual
endpoints, same producer witnesses, index recovery, all full-worker equations,
per-receipt histories and the supplied-hook boundary.

Evidence: lean/restart-evidence/20261026-native-selected-step.
The manifest records exact payload bytes and SHA-256 for raw logs, every
strict input, public readbacks, source snapshots, original Audit, proof diff,
verification report and cap records. The report also hashes all relevant
unchanged source files against the base commit. Force-add exactly the manifest
payloads. Verify indexed and committed bytes before the authorized push.

## Next composition

Wire the actual Left callback and a fuelled recursive selected step into
NativeContinuations. Use each receipt's own Caller/query/Post and branch cache.
Use initial dependency levels and pending-ID bounds to derive callback
completion. A pruning or stuck result completes that branch with no output;
it still retains all reached native effects before the next sibling.
Keep errors, unsupported outcomes and optional missing endpoints explicit.

The present SelectedStep still calls the old NativeOrdinary scan. Do not
postprocess an eagerly completed sibling list and call it source interleaving.
The new hook-aware fold must execute recursive continuation before evaluating
the next sibling. Each sibling restores the original captured enumeration
input and receives the same incoming metadata. Each callback's returned
metadata belongs to that branch's recursive continuation.

Derive initial-only native query capacity across narrowing, alternatives and
recursive calls. Extra fuel alone does not establish machine-word capacity.
Retain native Graph correspondence, terminal/nonordinary outer fallback,
pruning language laws, concrete solver behavior, extraction, finite-machine
correspondence and exact Haskell demand boundaries as open obligations.

''' + note[end:]
note = note.replace('PUBLIC_LINES',str(len(public.splitlines()))).replace('PUBLIC_BYTES',str(len(public)))
note = note.replace('PUBLIC_SHA','`'+hashlib.sha256(public).hexdigest()+'`')
(area/'handoff-content.json').write_text(json.dumps(dict(block=block,findings=findings,note=note),indent=2)+'\n')
