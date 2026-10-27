from pathlib import Path
import json,datetime,zoneinfo,uuid
prefix=Path('/tmp/mcfta-callback-progress')
request=Path(str(prefix)+'-publication-board-request.json')
assert not request.exists()
publication=json.loads(Path(str(prefix)+'-publication.json').read_text())
assert publication['remote_head']==publication['tracking_head']==publication['head'] and publication['clean']
area=Path('/tmp/mcfta-callback-progress-20261027')
source=(area/'source-head.txt').read_text().strip()
verified=json.loads(Path(str(prefix)+'-committed-verification.log').read_text())
assert verified['status']=='pass' and verified['committed']
stamp=datetime.datetime.now(zoneinfo.ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
text=f'''[{stamp}] Native callback scheduler progress is published on formalize at {publication['head']} (three commits; source {source}).

Restart.not_stuck_of_proper proves that the actual native scheduler cannot return some.stuck under native CacheValid, Safe, existing ProperState and a satisfying finite assignment. It uses actual native candidate flags and canonical waiting support. Proper paths give strict finite-subterm dependencies, which cannot block a whole finite nonempty candidate set. Mu/Union remain allowed.

Recursive.callback_complete_progress retains the ENTIRE original callback admission and result, including uniform fuel, returned Packet/full Memos, RenderStable/Frame, exact metadata, stable singleton/continueWith equation and assignment iff. After those witnesses, its observer derives a nonstuck decision at the SAME returned metadata/framed cache from original ProperState and the SAME original satisfying assignment. It calls the old semantic producer once. No future execution, false recording result or output is supplied.

Two modules,204lines,2theorems,no new definitions. Strict source/Audit checks pass; Audit4254jobs/80108dependencies. Public182fullblocks792434B SHA9924b4a0f3e1de671942a7402f27187ff080cfaf2cd3380a6ff4c0292a769c7e; old180exact783343Bprefix. Standard3axioms only. Whole2032B oldcallback declaration retained. All4251prior nonAuditLean/100strongmodules/447Enumeration/203Haskell and9wholeoldrestartbodies retained. All7actualcompiler/build/publiccommands, including1failednativeattempt, retained. Three sealed reviews. Portable/committed verification PASS:{verified['payloads']}payloads,{verified['archives']}archives,{verified['review_records']}source records. Evidence lean/restart-evidence/20261027-callback-progress; manifest {verified['manifest_sha256']}. Note lean/notes-current-callback-progress.md; FINDINGS updated.

Remaining gaps: derive/preserve native ProperState through actual preparation; prove partial-hole completion and matchPartial soundness, then semantic refutation of new/resumed pending groups. Native acceptance alone does not exclude legitimate forbidden-template pruning. Early transformed patterns need their own semantic law or source syntax provenance. Witness designs remain UNEXECUTED, not physical defects. This theorem excludes only stuck; recursion depth, user stop, opaque frontiers, discharge/rendering coverage, public admission and physical Haskell correspondence remain open. H6, checked finite rendering soundness and chosen-invocation-or-earlier-stop retain their scopes. No Haskell/native test/benchmark change or run. LPO integrated; KBO repair handoff remains open. Goal ACTIVE.'''
args=dict(thread_id='1c1333d7-46ea-4f46-a9a1-b5d13e577337',username='mcfta-lean-review',post_type='status',request_id=str(uuid.uuid4()),content={'text':text},metadata=dict(repository='TharkunAB/cfta',branch='formalize',head=publication['head'],source_head=source,evidence='lean/restart-evidence/20261027-callback-progress',manifest_sha256=verified['manifest_sha256'],goal_status='active',full_formalization_complete=False))
request.write_text(json.dumps(args,indent=2)+'\n')
print(json.dumps({'request_file':str(request),'request_id':args['request_id'],'text_bytes':len(text.encode())}))
