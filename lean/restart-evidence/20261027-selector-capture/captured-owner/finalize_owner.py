from pathlib import Path
import json,hashlib,datetime
root=Path('/home/tritlo/Code/mcfta');stage=Path('/tmp/mcfta-selector-capture-20261027');a=stage/'captured-owner'
assert not (a/'FROZEN.json').exists()
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
idx=json.loads((a/'source-index.json').read_text())
def cap(p,rel):
 b=p.read_bytes();dest=Path(rel);(a/dest).parent.mkdir(parents=True,exist_ok=True);(a/dest).write_bytes(b)
 idx['sources'].append({'source':str(p),'whole':{'path':str(dest),**ident(b)},'cuts':[]})
cap(stage/'document-validation.json','final/documents/document-validation.json')
val=json.loads((stage/'document-validation.json').read_text());inverses=[];regions=[]
for r in val:
 p=root/r['path'];b=p.read_bytes();assert ident(b)=={'bytes':r['bytes'],'sha256':r['sha256']}
 if 'offset' not in r:
  assert r['path']=='lean/notes-current-selector-capture.md' and len(b)==10650 and r['sha256']=='010db0432469065ab4468fd76dffac9fda3d2c8ff93a0ee97d177b76c5b23d54'
  cap(p,'final/documents/notes-current-selector-capture.md');continue
 offset=r['offset'];length=r['inserted_bytes'];cut=b[offset:offset+length];old=b[:offset]+b[offset+length:]
 baseline=stage/'prior-documents'/r['path'];assert old==baseline.read_bytes()
 first=b[:offset].count(b'\n')+1;last=b[:offset+length].count(b'\n')
 assert b''.join(b.splitlines(keepends=True)[first-1:last])==cut
 cp=Path('final/documents/inserted-cuts')/(r['path'].replace('/','--')+f'.L{first}-L{last}.txt')
 (a/cp).parent.mkdir(parents=True,exist_ok=True);(a/cp).write_bytes(cut)
 idx['sources'].append({'source':str(p),'bytes':len(b),'sha256':r['sha256'],'cuts':[{'path':str(cp),**ident(cut),'first_line':first,'last_line':last}]})
 inverses.append({'source':str(p),'source_bytes':len(b),'source_sha256':r['sha256'],'removed_offset':offset,'removed_bytes':length,'prior_source':str(baseline),'recovered':ident(old),'prior':ident(baseline.read_bytes()),'literal_equal':True})
 regions.append(cut)
assert len(inverses)==9
common=next(x for x in regions if len(x)==2144);assert all(x==common for x in regions if len(x)==2144)
assert next(x for x in regions if len(x)==3064).startswith(common)
(a/'final/documents/inverse-validation.json').write_text(json.dumps({'status':'PASS','checked_at':datetime.datetime.now().astimezone().isoformat(),'all_nine_prior_bodies_literal_equal':True,'eight_status_insertions_literal_equal':True,'findings_starts_with_same_status_region':True,'common_region':ident(common),'inverses':inverses},indent=2)+'\n')
(a/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
# Validate each retained copy and each literal source/public/document cut.
for r in idx['sources']:
 if 'whole' in r:
  w=r['whole'];assert ident((a/w['path']).read_bytes())=={'bytes':w['bytes'],'sha256':w['sha256']}
 for c in r['cuts']:
  assert ident((a/c['path']).read_bytes())=={'bytes':c['bytes'],'sha256':c['sha256']}
mods=json.loads((stage/'modules.json').read_text())
source_bytes=sum(len((root/'lean/MicroCFTA'/f'{m}.lean').read_bytes()) for m in mods)
source_lines=sum(len((root/'lean/MicroCFTA'/f'{m}.lean').read_text().splitlines()) for m in mods)
assert source_bytes==35196 and source_lines==536
(a/'report-before-final.txt').write_bytes((a/'report.txt').read_bytes())
report=f'''CLEAR — final captured coverage and selector consumer review

Measured final review time: {datetime.datetime.now().astimezone().isoformat()}
Final source checkpoint: 82fdb41fc9e55f57e2950ab78297140cbdc97c69.

The owned theorem SourcePruningEnumerationCapturedEdge.complete_with_history_resources_accepting retains the ENTIRE original CapturedEdgeResources admission, operational witnesses and result packet. Its added observer is universal AFTER the operational bounds and original fields. Removing only that observer and restoring the old name recovers the full original 4422-byte proposition, SHA256 d8aa8f57c56aef994c44bc9b183b4fad5948280e68f7ab51b2647ff8baa8a529. Exact original/new/recovered propositions and the comparison receipt remain in contract-comparison/.

The observer takes original Satisfies under the actual native PCSGuard residual interpretation and selected-edge acceptance at assignment uv. The original stored pending model derives ALL inherited Holds. The accepting SelectedEdge producer is called ONCE. It constructs the middle model and fragment at the SAME native caller/full Memos/query/cache witnesses. Actual Finalize.complete is called ONCE in the completed arm. The old raw slot, history, protected roots, indexes, resource bounds, ancestry reset and stratified order conclusions remain unchanged. Old-variable agreement includes ready captured uv, so fill extended fragment = assignment uv = extended uv. neutralize_satisfies and actual written_semantics then derive satisfaction of the SAME finalized cache. No final satisfaction, desired extension, future successful execution, Canonical, backward retention or universal Ranges premise is introduced. The original stopped packet remains intact; a supplied accepted model contradicts that result constructor and supplies no Safe-on-rejection fact.

The entire Root selected_parent_complete wrapper was independently read. Its original stored model derives native parent acceptance and every inherited suspended constraint. Actual selectedRows.Perm provides an accepted edge in BOTH actual selected and resident lists, with real residency. selected_admission derives current successful guard projection and inherited arity. The original reservation covers selected current edges and their unique CURRENT pure projection, not future execution. The wrapper calls the primary captured producer ONCE and applies its retained observer. Its chosen model precedes its chosen edge and operational bounds; the retained primary observer remains universal after those bounds. The complete primary existential/result+observer recovers literally from the wrapper after removing only explicit grouping and the chosen-model completion appendix: 4049 bytes, SHA256 ba9810146e5944e3384006e7abf12dd15e8d2f658e23ddd98b4373d8441f2ead. No claim is made that the semantic-facing wrapper's header is identical to the primary header. Exact comparison and full source review remain in wrapper-contract-comparison/ and wrapper-review/.

All five complete NEW public signature/axiom blocks were read, 469 lines and 36507 bytes. The complete public output is retained as evidence without a claim to reread every historical block: 667078 bytes, SHA256 4453ff071f4251bd7b753e880e0301ccdc5c1eed804c34a416d7fece799ee2a5. Its entire 630571-byte/168-block prior prefix is literally equal. Root's validation records 90 prior modules unchanged; preservation-validation records 437 existing enumeration sources and 203 Haskell sources unchanged. The three new modules contain 536 lines and 35196 source bytes, declare five theorems, and add no definition, predicate or structure. Only propext, Classical.choice and Quot.sound occur. Raw interned selection directly retains its resident edge. The modeled canonical closure retains acceptance only under its explicit actual map-or-fallback row permutation; physical canonical map construction and source sorting remain separate.

Captured primary v1 is 279 lines, 18027 bytes, SHA256 3c9f9fe36b8ba52093040a37821c83b88086182576dafa53df77757565d49218. Draft, successful strict snapshot and installed source are byte identical. Its first strict check passes with zero output. The unchanged parent wrapper is 176 lines, 12412 bytes, SHA256 16abe9176f409bdcbde2f930f5a914db42fba12cd8717a20920ae766cbfff5e2; its first strict check also passes with zero output. The selector final source matches successful strict-selector-2; its earlier failure and proof-only repair are preserved in Root's separate selector bundle, not represented as successful here. All bound successful strict checks use warningAsError=true, linter.all=true, measured 4 GiB memory.max/high and zero swap. The selector+primary build passes 1901 jobs. Full Audit passes 4245 jobs and checks 80074 theorem dependencies. Its known replayed old dependency warning is retained in full. Standalone strict Audit passes with its expected 56-byte count line. This worker ran no compiler, evaluator, build or native test.

The full final note was read: lean/notes-current-selector-capture.md, 10650 bytes, SHA256 010db0432469065ab4468fd76dffac9fda3d2c8ff93a0ee97d177b76c5b23d54. All nine complete inserted regions, including FINDINGS' extra handoff paragraph, were read. Eight status regions are literally equal and FINDINGS begins with the same region. Every inverse removal independently equals its exact prior-documents baseline bytes. The note is stored as a whole copy. Inserted regions are labeled cuts with exact source/full identity and one-based inclusive line bounds; none is described as a whole status-document copy.

Strongest current claim: an original satisfying ready stored ordinary parent, under the explicit current native/enum/resource admission and selector permutation, supplies an accepted selected edge and a completed actual CAPTURED CALL with the same assigned captured value. It does not prove the ordered NativeBranches or NativeContinuations scan reaches that occurrence. An earlier arity-allowed projection=None can stop NativeBranches; an earlier hook can stop NativeContinuations. Actual earlier native caller/full-Memos effects and fixed captured-cache restoration must be retained in a later scan proof. No desired future invocation is admitted here. Full recursive coverage, frontier expansion, Discharged and concrete rendering coverage, physical canonical storage/sorting, remaining public API admission and full Haskell correspondence remain open. H6 and the earlier conditional finite rendering soundness keep their exact previous scopes. No new physical Haskell defect follows. No Haskell source, Cabal file, native test or benchmark changed or ran. Existing Haskell repair handoffs and the unintegrated/unbuilt/unexecuted KBO candidate remain separate. The whole goal remains ACTIVE.

Publication condition: Root must create and validate the immutable archive after this review and live preflight. Frozen-byte and committed-byte validation must pass before push. This report does not assert archive creation, committed validation or publication has occurred. Those receipts remain future and outside the frozen review.

Only /tmp/mcfta-selector-capture-20261027/captured-owner was written by this worker. No earlier frozen area or repository file was modified. Exact input whole copies, literal cuts, source-only initial proposal/report, strict/build/public output and contract comparisons remain. This bundle is sealed after this report and no further writes are permitted.
'''
(a/'report.txt').write_text(report)
(a/'final-prose-review.json').write_text(json.dumps({'status':'CLEAR','reviewed_at':datetime.datetime.now().astimezone().isoformat(),'source_head':'82fdb41fc9e55f57e2950ab78297140cbdc97c69','whole_note':{'source':str(root/'lean/notes-current-selector-capture.md'),**ident((root/'lean/notes-current-selector-capture.md').read_bytes())},'inserted_regions_read':9,'all_old_body_inverses_literal_equal':True,'archive_committed_push':'future; not claimed'},indent=2)+'\n')
# Exact payload set: exclude only this owner's root manifest and root seal.
exclude={a/'pins.json',a/'FROZEN.json'}
files=sorted(p for p in a.rglob('*') if p.is_file() and p not in exclude)
payloads=[{'path':str(p.relative_to(a)),**ident(p.read_bytes())} for p in files]
pinsb=(json.dumps({'payloads':payloads},indent=2)+'\n').encode();(a/'pins.json').write_bytes(pinsb)
seal={'status':'FROZEN','sealed_at':datetime.datetime.now().astimezone().isoformat(),'source_head':'82fdb41fc9e55f57e2950ab78297140cbdc97c69','pins_sha256':hashlib.sha256(pinsb).hexdigest(),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'excluded_only':['pins.json','FROZEN.json'],'source_records':len(idx['sources']),'literal_cuts':sum(len(r['cuts']) for r in idx['sources']),'report_sha256':ident((a/'report.txt').read_bytes())['sha256']}
(a/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
# All operations after seal creation are read-only.
actual={str(p.relative_to(a)) for p in a.rglob('*') if p.is_file()}
assert actual=={p['path'] for p in payloads}|{'pins.json','FROZEN.json'}
assert len(actual)==seal['exact_file_count']
for p in payloads:assert ident((a/p['path']).read_bytes())=={'bytes':p['bytes'],'sha256':p['sha256']}
assert ident((a/'pins.json').read_bytes())['sha256']==seal['pins_sha256']
print(json.dumps({'manifest':str(a/'pins.json'),'seal':str(a/'FROZEN.json'),**seal,'seal_sha256':ident((a/'FROZEN.json').read_bytes())['sha256']},indent=2))
