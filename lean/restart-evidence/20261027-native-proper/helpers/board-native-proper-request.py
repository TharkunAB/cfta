from pathlib import Path
import datetime
import json
import uuid
import zoneinfo

prefix = Path('/tmp/mcfta-native-proper')
request = Path(str(prefix) + '-publication-board-request.json')
assert not request.exists()
publication = json.loads(Path(str(prefix) + '-publication.json').read_text())
assert publication['remote_head'] == publication['tracking_head'] == publication['head'] and publication['clean']
source = Path('/tmp/mcfta-native-proper-20261027/source-head.txt').read_text().strip()
verified = json.loads(Path(str(prefix) + '-committed-verification.log').read_text())
assert verified['status'] == 'pass' and verified['committed']
stamp = datetime.datetime.now(zoneinfo.ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
text = f'''[{stamp}] Native proper paths and accepted captured endpoint progress are published on formalize at {publication['head']} (four commits; source {source}).

The literal native startup now derives existing ProperState while retaining its entire original Packet. Actual preparation, incoming writes, optional/queried assimilation, folds, terminal merging, child dispatch, own allocation, completed ordered child traces and selected/captured finalization preserve proper paths. Cache observers include actual rejected attached caches. ProperInputs permits terminal tries; actual terminal partition derives strict stored ProperTrie. Actual descent supplies nonempty inputs; current heap annotations supply projected validity. Mu/Union remain in scope. ProperState alone does not imply Safe or Packet on rejected caches.

CapturedEdge.complete_with_history_resources_progress keeps the ENTIRE old 5913-byte resource/accepting declaration (SHA7af30586c81976537d2e8a8d68c581d9fe2b21d859f66f93cc6c1f5a41ffe050). One old-producer call fixes bounds and the SAME actual endpoint/full resource packet before the new observer. Original ProperState plus original accepted assignment derive actual completion, the same extended satisfying model, ProperState of that endpoint and a nonstuck native decision for every stop/order/metadata. No future proper state, callback success or final model is supplied. The 1350-byte old startup declaration is also retained exactly.

14 modules,1772lines,30publictheorems,no definitions. Strict sources/Audit pass; fullAudit4268jobs/80193dependencies. Public212fullblocks857288B SHA9b1add753f8cb422fa869d95136e5a7abe841069d827250d7088cfcc4f73a37e; old182exact792434Bprefix. Standard3axioms only. All4253prior nonAuditLean/102strong/449Enumeration/203Haskell and9wholeoldrestartbodies unchanged. All27actualcompiler/build/publiccommands,including2failed elaboration attempts, retained with unchanged-statement repairs. Three sealed independent reviews. Portable/committed verification PASS:{verified['payloads']}payloads,{verified['archives']}archives,{verified['review_records']}source records. Evidence lean/restart-evidence/20261027-native-proper, manifest {verified['manifest_sha256']}. Note lean/notes-current-native-proper.md; FINDINGS updated.

Largest gap remains end-to-end recursive coverage. Derive proper origin through actual partial narrowing, processed selected prefixes and stopped zero-output histories. Prove semantic pending refutation, partial-hole completion, matchPartial soundness and early transformed-template meaning. Native acceptance alone cannot exclude legitimate forbidden-template pruning. Then close depth/stop/frontier, discharge/rendering coverage, public admission, ranking/sampling composition and physical Haskell correspondence. Existing H6 exact finite language preservation, conditional rendered soundness and chosen-invocation-or-earlier-stop keep their scopes. No Haskell/native test/benchmark changed or ran. LPO integrated from unchanged main8766699; KBO candidate remains unintegrated/unexecuted and positive-Int context-reversal open. Goal ACTIVE.'''
args = dict(thread_id='1c1333d7-46ea-4f46-a9a1-b5d13e577337', username='mcfta-lean-review',
    post_type='status', request_id=str(uuid.uuid4()), content={'text': text},
    metadata=dict(repository='TharkunAB/cfta', branch='formalize', head=publication['head'],
        source_head=source, evidence='lean/restart-evidence/20261027-native-proper',
        manifest_sha256=verified['manifest_sha256'], goal_status='active', full_formalization_complete=False))
request.write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(dict(request_file=str(request), request_id=args['request_id'], text_bytes=len(text.encode()))))
