from pathlib import Path
import json,datetime,hashlib,re
r=Path('/home/tritlo/Code/mcfta');h=r/'lean/restart-evidence/20261020-native-active-result-lineage'
proof=(h/'proof-commit.txt').read_text().strip();stamp=datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
# The host default zone can differ from the user's zone.
from zoneinfo import ZoneInfo
stamp=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
unique={}
for p in h.rglob('*.json'):
 try:d=json.loads(p.read_text())
 except ValueError:continue
 if isinstance(d,dict) and isinstance(d.get('command'),list) and isinstance(d.get('exit_code'),int) and 'wrapper' in d and Path(d['command'][0]).name in ['lean','lake']:unique.setdefault(json.dumps(d,sort_keys=True),[]).append(str(p.relative_to(h)))
commands=len(unique);fails=sum(json.loads(k)['exit_code']!=0 for k in unique)
assert commands==42 and fails==5,(commands,fails)
shared=f'''## Current terminal writers and earlier captured Mu producers

Updated: {stamp}. Proof checkpoint: `{proof[:9]}`.
Verified start: `eb13a888d`. Main remains `9769fe3e9`.
Read `lean/notes-current-native-active-result-lineage.md`.

A new full Mu in bounded checked node execution now retains its same
optional instruction, queried evaluating owner and actual entered child.
That child's nonempty result retains a terminal returned cell and strong
historical writer at the same site. The terminal handle differs from that
owner's evaluating handle. Blocked nested construction remains covered.
The terminal writer produces the child result, not the generated stored body.

Actual prefix writer maps now support active row and Mu body origins
without History at the active reader. The row theorem preserves actual
source row and child indices. The Mu theorem preserves its supplied
historical writer. Warm forwarding can use historical compiler traces.
It does not assert that all forwarding hops ran in the current child call.

An indexed full Mu in the actual captured leaf pool is present at entry
or has a strictly earlier generating optional instruction in the same
prefix. That earlier instruction retains its generated source writer and
terminal child origin. The index is a leaf occurrence, not encode.slot.
Initial cells are original-source cells only when the actual closed source
build returns exactly the native entry heap. A separate source-scope theorem
retains original execution writers under that exact equality.

One compiled example derives its source construction, guard allocation,
Good, History and checked schedule. Two distinct recursive operands produce
a new used Mu. One generation application retains the same full owner,
child, terminal cell and writer tuple. Eleven public and one constructed
full declaration readbacks pass. Seven selected module strict logs and
the fixture strict log are empty. Default build: 3518 jobs and 74224 axiom
checks. Only the earlier ClosedCompletion unused-input warning remains.
All {commands} capped Lean/Lake commands and {fails} failed attempts are retained.
Two successful warning attempts remain unselected. Receipt copies add no jobs.

Closed NODE capture producers and original program ancestry remain open.
The strict decrease orders actual past producers. It is not an outer runtime
rank. Global renewal, global active-owner exclusion, final owner retention,
general completion, convergence and Haskell refinement remain open.
Conditional root-language and Sized laws are unchanged. All 268 Haskell
files and all 207 active package files retain their bytes. FINDINGS keeps
external repairs first. No new Haskell repair or runtime validation is claimed.
The full-library goal stays active. Publication to formalize is authorized.

'''
common=['NEXT-PROMPT.md','HANDOFF.md','lean/README.md','lean/SYSTEM.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/notes-proof-status-20261017.md','lean/notes-current-system-claim.md']
for n in common:
 p=r/n;text=p.read_text();i=text.index('\n\n')+2;p.write_text(text[:i]+shared+text[i:])
update=f'''Current proof update: {stamp}. Proof checkpoint: `{proof[:9]}`.
New generated full Mu cells now retain their same optional instruction,
evaluating owner, entered child and terminal returned writer. That terminal
handle differs from the same owner's handle. Active row and Mu body origins
use actual prefix writer maps without internal History. Indexed captured Mu
cells are exact initial cells or have a strictly earlier actual optional
producer with the same generated source writer and terminal origin.
An actual compiled example creates a new used Mu from distinct recursive
operands. Eleven public and one constructed full readbacks pass. Seven
module strict logs and the fixture strict log are empty. Default build:
3518 jobs and 74224 axiom checks. All {commands} capped commands and {fails} failures
remain. Two successful warning attempts stay unselected. Closed NODE capture
producers, original program ancestry, global renewal and busy-owner exclusion,
final owner retention, general completion, convergence and Haskell refinement
remain open. No new Haskell repair or runtime validation is claimed.
All 268 Haskell files and all 207 active package files retain their bytes.
Read `lean/notes-current-native-active-result-lineage.md`.
Preserve every external repair, reproducer and validation result below.

'''
p=r/'FINDINGS.md';text=p.read_text();i=text.index('Current proof update:');p.write_text(text[:i]+update+text[i:]);(h/'findings-update.md').write_text(update)
note='''# Native active result lineage and captured Mu chronology

'''+shared+'''## Exact public contracts

- `SourceCurrentNativeActiveQueryForwarding.forwarded` derives a completed child's `Forwarded` receipt at a retained reader. Its caller supplies the reader's strong returned-node writer map. `normalize` follows actual swap and reset writer bodies to a terminal returned cell for the same nonempty result. It derives both input codecs. It requires no completed History at the reader.
- `SourceCurrentNativeActiveRowOrigins.child` derives both writer maps from one actual clean prefix. A selected ordinary returned node row retains its original left and right source row indices. A selected child retains both ordered source child lookups, its strong edge writer, checked child call, retained final cell and forwarding receipt. The node writer is chosen from the cell-indexed map. The theorem does not equate that writer witness with an independently supplied normalization witness.
- `SourceCurrentNativeOriginalRequestScope.RootedScope` describes original execution writers for queried Mu operands and named bindings. `optional` derives this scope for every actual earlier queried node in the same closed-root prefix. It uses one recovered raw owner tuple. The original closed build must return exactly the native entry heap. Later heap growth does not supply this equality.
- `SourceCurrentNativeOptionalTerminalOrigin.Origin` keeps the full raw owner tuple and appends the same entered child's terminal Route, returned cell, strong writer, both codecs, non-swap and non-reset facts, and terminal-handle inequality. `request` derives this receipt from an actual optional prefix, initial Good and History, and a nonempty child result. The inequality follows from the owner's evaluating phase and the terminal cell's returned phase at the same site.
- `SourceCurrentNativeActiveMuBodyOrigins.trace` derives the actual entered body call of a completed Mu compiler trace. `returned` preserves the supplied historical strong writer's exact entry, child call, optional construction and retention. The same-reader map derives child forwarding. No active child-entry History is supplied.
- `SourceCurrentNativeTerminalGeneration.execute` applies stopping generation once. Each new selected full Mu retains the exact same optional prefix, done or pending source call, generated source build and rooted writer. Its same prefix supplies the stronger terminal origin. The used intersection placeholder derives the nonempty premise. Exact initial full cells remain a separate alternative.
- `SourceCurrentNativeCapturedMuOrigins.capture` selects one indexed full Mu in `leaves siteBody`. Actual leaf availability derives its exact resident full cell. One optional-generation application returns the exact initial full cell or the same earlier optional instruction, source build and rooted writer. It retains the actual prefix and suffix and proves `earlierPrefixFuel < currentFuel`. The same earlier prefix supplies its terminal owner/child origin. Initial Good, History, SemanticHeap, the actual current checked prefix and current body availability remain explicit.

The terminal Route can contain historical writer traces used by a warm cache result. Those traces need not form a contiguous subtrace of the current child call. Its fuel is not charged to the current childFuel. The terminal result writer and the generated Mu's source build writer have different roles. The proofs retain both roles.

## Actual compiled generation example

The source builds one closed pair wrapper with two distinct recursive operands. Each operand has a recursive row and a different nullary row. Their intersection retains the common recursive row. Its repeated pair reference remains free at optional construction. The checked run creates a full Mu whose cell is absent initially and present finally. Its stored body uses its own interned binder.

The fixture derives the source construction, root and child availability, closed operands, guard field allocation, validity, Fields, Good, initial History and semantic readiness. An actual successful bounded run supplies its raw steps. Prefix admission derives the checked schedule. One TerminalGeneration application excludes the exact initial-cell alternative and retains one correlated generated tuple. The public type expands the full owner, entered child, terminal Route, cell, writer, codecs and distinct handles. It does not force that existential owner to be a particular top-level query.

The older generation fixture is retained as a validated predecessor. The stronger fixture is selected for this checkpoint's constructed readback. This is one actual example with two preserved proof versions. It does not exercise a noninitial captured Mu leaf. A future example can use outer recursive rows whose second child is an intersection of two distinct inner recursive operands. The inner result can then become an actual captured Mu of the outer optional instruction. Derive and check that case before claiming it as evidence.

## Verification and preservation

All selected declarations have complete statement, proof and axiom readbacks. The eight printer options are explicit. Only propext, Classical.choice and Quot.sound are admitted. The seven selected module strict logs and selected fixture strict log are empty. Every selected source has a canonical target build. The final default audit covers 3518 jobs and 74224 axiom dependency checks. Only the older ClosedCompletion unused-input warning remains.

The evidence directory retains all actual capped commands, source snapshots, raw logs, usage samples, effective cgroup limits, failures and successful unselected attempts. Duplicate copies of a receipt do not count as new commands. The first default audit preceded the additional capture theorem. The second default audit checks the final seven-module scope. Failed attempts and the rejected fixture metadata remain historical evidence. The final selections exclude both warning runs.

The source proof commits are recorded in proof-commits.json. The current proof authority is proof-commit.txt. Publication and post-push closure receipts stay outside the sealed committed evidence to avoid self-reference. The closure must verify tracked bytes and modes against both the index and HEAD, all evidence checksums, remote formalize equality and unchanged remote main.

## Top-level result and remaining work

The top-level language theorem remains `SourceCurrentConstructedRootCall.root_call`. Fresh construction terminates in the Lean model. Under the stated guard and resource conditions, it builds the expression's exact finite-tree language. A successful supported modeled root reduction with empty inherited constraints preserves that language. Logical startup facts are derived. Field allocation, validity, guard coverage and numeric resources remain explicit. The existing conditional Sized count, rank, unrank, class and prefix laws are unchanged.

The current native results improve provenance of actual executions. They do not prove whole-library Haskell correspondence or unconditional recursive execution. General outer termination and the original renewal argument still require a rank that applies before the next call finishes.

The next ancestry obligation is an indexed producer for arbitrary closed NODE leaves assembled by native row intersection. The collector stops at a closed value. That whole value can be a new intersection result rather than either source operand. ActiveRowOrigins retains the required source rows and child calls, but it does not yet propagate a leaves occurrence through each native constructor and the closed-value stopping rule. Do not replace this obligation with a desired leaf-ancestry premise.

For full Mu captures, strict prior-prefix descent now supplies an actual chronological relation. An initial captured cell has an original execution writer only when the actual original closed build returns exactly the native entry heap. A preceding Head or native interval needs its own producer. Native heap growth and completed memo History do not prove original source ancestry.

Stored unfolds use mapped self environments over stored-body leaves. Their canonical slot and self classifications remain separate from the native optional leaf pool. Selected historical winners retain their actual publication. Do not replace them with the current callback. Original binding paths, global active-owner exclusion, final owner retention, renewal, convergence, general outer completion and end-to-end Haskell refinement remain open.

All production Haskell and active package files are unchanged. Keep every verified Haskell repair in root FINDINGS before any repair edit. The End False field-pool invariant defect is fixed upstream. The Typing.hs size-order wording candidate remains unvalidated because the isolated cached-toolchain reproducer failed before rank output. Do not classify that blocker as a runtime defect.
'''
(r/'lean/notes-current-native-active-result-lineage.md').write_text(note)
documents=common[:2]+['FINDINGS.md']+common[2:]+['lean/notes-current-native-active-result-lineage.md','lean/MicroCFTA/Audit.lean'];(h/'current-documents.json').write_text(json.dumps(documents,indent=2)+'\n')
(h/'attempt-accounting.json').write_text(json.dumps({'capped_commands':commands,'failed_commands':fails,'successful_unselected_warning_commands':2,'receipt_copies_add_commands':False,'commands':[{'receipt':json.loads(k),'copies':v} for k,v in unique.items()]},indent=2)+'\n')
(h/'root-review.md').write_text('''# Selected source review

No material issue was found in the selected seven-module scope. ActiveRowOrigins and OriginalRequestScope have independent complete source reviews. OptionalTerminalOrigin and TerminalGeneration have a separate independent review of the same owner and child tuple. CapturedMuOrigins and the stronger actual generation fixture also have independent complete source reviews. The root review checked the selected source snapshots, literal empty strict logs, full printer outputs, axiom reports and canonical target receipts.

The active row result is cell-indexed. It does not identify an independently supplied node writer witness. The Mu body result preserves its supplied writer. Route hops can be historical. The local handle inequality is not global active-owner exclusion. The terminal result writer is not a generated stored-body writer. Captured Mu chronology is a strict relation on an actual past execution prefix. It is not a future runtime rank. Initial exact cells are original-source cells only under exact original source construction of that initial heap. Arbitrary closed NODE capture producers remain open.
''')
print(json.dumps({'proof':proof,'documents':len(documents),'commands':commands,'failed':fails,'updated':stamp}))
