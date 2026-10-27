from pathlib import Path
import datetime
import json
import uuid
import zoneinfo

prefix = Path('/tmp/mcfta-native-history-proper')
request = Path(str(prefix) + '-publication-board-request.json')
assert not request.exists()
publication = json.loads(Path(str(prefix) + '-publication.json').read_text())
assert publication['remote_head'] == publication['tracking_head'] == publication['head'] and publication['clean']
source = Path('/tmp/mcfta-native-history-proper-20261027/source-head.txt').read_text().strip()
verified = json.loads(Path(str(prefix) + '-committed-verification.log').read_text())
assert verified['status'] == 'pass' and verified['committed']
stamp = datetime.datetime.now(zoneinfo.ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
text = f'''[{stamp}] Proper emitted histories and the KBO Natural repair are published on formalize at {publication['head']}; source {source}.

Recursive.run_initial_finite_render_sound_proper retains the ENTIRE old startup declaration and adds ProperState for every SAME actual emitted output cache. No new producer admission, input invariant or semantic model is supplied. Literal startup and each emitted output's actual ResourceHistory derive proper storage through partial narrowing, parked steps, ordinary entry, completed heads and callbacks. Canonical, fixed bounds, actual outcome, full resources and conditional checked rendering soundness remain. This closes proper origin for emitted recursive outputs. Aggregate zero-output cache history remains separate.

Local resource wrappers cover proper attached complete AND stopped child/traversal/selected/captured caches. Native scans observe every processed receipt's own cache with actual callers/full Memos. Eight complete old declarations are retained literally after rename/grouping/appended observer (3737,4287,4184,4422,2705,3903,4589,4647 bytes). Seven call the original producer once; native branch follows the actual old head induction. No desired future execution is assumed.

14modules,1727lines,21new public theorems,no definitions. Strict sources/Audit PASS; full Audit4282jobs80232dependencies. Public233completeblocks971561B SHA0b4a5aba1c25b8639bf967c96d9773df57a887fd7621e616044cc327a245d58a; prior212exact857288Bprefix. Three standard axioms only. All4267oldnonAuditLean/116strong/463Enumeration preserved. All34actualcommands,including7failed Lean attempts and final repairs, retained; serial4GiBswap0. Three independently sealed reviews. Portable/committed verification PASS: {verified['payloads']}payloads,{verified['archives']}archives,{verified['review_records']}source records. Evidence lean/restart-evidence/20261027-native-history-proper; manifest {verified['manifest_sha256']}. Note lean/notes-current-native-history-proper.md; nine entire old restart bodies preserved.

Main d1ca06a1dd0c7488205feda613b529df21a08669 and KBO repair d7b6a9dfff464eb32c17c314d4825d5b027f1b2d are integrated. Two imported Haskell files equal main;201others unchanged. Definition weights use Natural/lazyMap. Existing golden suite/context regression PASS. Actual prior public-API witness now GT/GT; computed weights0..63 equal exactInteger recurrence through18446744073709551615. Specific Int-weight context reversal is repaired. General KBO laws/rewrite termination/physical pruning correspondence remain open. Formatting/cabal-gild and native checks PASS in nix-shell; no benchmark/local Haskell edit. FINDINGS has the current repaired status before historical open reports. Prior LPO/extraction fixes remain integrated.

Largest gap remains end-to-end enumeration coverage. Prove semantic pending refutation, partial-hole completion and matching, early transformed-template meaning, depth/stop/frontier/projection policies, discharge/rendering coverage, public admission, ranking/sampling composition and physical Haskell correspondence. Automaton acceptance does not exclude legitimate forbidden-template pruning. H6 exact finite pruning preservation and chosen-invocation-or-earlier-stop keep their scopes. Goal ACTIVE; whole formalization incomplete.'''
args = dict(thread_id='1c1333d7-46ea-4f46-a9a1-b5d13e577337', username='mcfta-lean-review',
    post_type='status', request_id=str(uuid.uuid4()), content={'text': text},
    metadata=dict(repository='TharkunAB/cfta', branch='formalize', head=publication['head'],
        source_head=source, evidence='lean/restart-evidence/20261027-native-history-proper',
        manifest_sha256=verified['manifest_sha256'], goal_status='active', full_formalization_complete=False))
request.write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(dict(request_file=str(request), request_id=args['request_id'], text_bytes=len(text.encode()))))
