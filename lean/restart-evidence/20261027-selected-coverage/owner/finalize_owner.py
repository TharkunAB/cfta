from pathlib import Path
import hashlib,json,datetime
root=Path('/home/tritlo/Code/mcfta');stage=Path('/tmp/mcfta-selected-coverage-20261027');a=stage/'owner'
assert not (a/'FROZEN.json').exists()
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
index=json.loads((a/'source-index.json').read_text())
def capture(source,snapshot):
 b=source.read_bytes();sp=Path(snapshot);(a/sp).parent.mkdir(parents=True,exist_ok=True);(a/sp).write_bytes(b)
 index['sources'].append({'source':str(source),'snapshot':str(sp),**ident(b),'cuts':[]})
 return b
for name in ['document-validation.json','root-document-validation.json']:
 capture(stage/name,f'final/documents/{name}')
validation=json.loads((stage/'document-validation.json').read_text());inverses=[];regions=[]
for r in validation:
 source=root/r['path'];b=source.read_bytes();assert ident(b)=={'bytes':r['bytes'],'sha256':r['sha256']}
 if 'offset' not in r:
  assert r['path']=='lean/notes-current-selected-coverage.md' and len(b)==10380
  assert ident(b)['sha256']=='8ada69c850ab52921f5ff453ab20fa220e0b05da81adb2b544fe9eebac65d559'
  capture(source,'final/documents/notes-current-selected-coverage.md')
  continue
 offset=r['offset'];size=r['inserted_bytes'];cut=b[offset:offset+size]
 old=b[:offset]+b[offset+size:];baseline=stage/'prior-documents'/r['path']
 assert old==baseline.read_bytes() and ident(old)=={'bytes':r['prior_bytes'],'sha256':r['prior_sha256']}
 first=b[:offset].count(b'\n')+1;last=b[:offset+size].count(b'\n')
 assert b''.join(b.splitlines(keepends=True)[first-1:last])==cut
 cp=Path('final/documents/inserted-cuts')/(r['path'].replace('/','--')+f'.L{first}-L{last}.txt')
 (a/cp).parent.mkdir(parents=True,exist_ok=True);(a/cp).write_bytes(cut)
 record={'source':str(source),**ident(b),'cuts':[{'snapshot':str(cp),'first_line':first,'last_line':last,**ident(cut),'source_sha256':r['sha256']}]}
 index['sources'].append(record)
 inverses.append({'source':str(source),'source_bytes':len(b),'source_sha256':r['sha256'],'removed_offset':offset,'removed_bytes':size,'baseline_source':str(baseline),'recovered':ident(old),'literal_equal':True})
 regions.append(cut)
assert len(regions)==9
common=next(x for x in regions if len(x)==2022)
assert all(x==common for x in regions if len(x)==2022)
assert next(x for x in regions if len(x)==2750).startswith(common)
(a/'final/documents/inverse-byte-validation.json').write_text(json.dumps({'status':'PASS','measured_at':datetime.datetime.now().astimezone().isoformat(),'nine_insertions':inverses,'common_region':ident(common),'all_eight_ordinary_regions_literal_equal':True,'findings_contains_same_region_then_explicit_handoff_status':True},indent=2)+'\n')
(a/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
# Verify every copied whole source and literal cut before sealing. Live files remain read-only.
for r in index['sources']:
 if 'snapshot' in r:
  assert ident((a/r['snapshot']).read_bytes())=={'bytes':r['bytes'],'sha256':r['sha256']}
 for c in r.get('cuts',[]):
  assert ident((a/c['snapshot']).read_bytes())=={'bytes':c['bytes'],'sha256':c['sha256']}
  assert c['source_sha256']==r['sha256']
mods=json.loads((stage/'modules.json').read_text())
module_bytes=sum(len((root/'lean/MicroCFTA'/f'{m}.lean').read_bytes()) for m in mods)
module_lines=sum(len((root/'lean/MicroCFTA'/f'{m}.lean').read_text().splitlines()) for m in mods)
assert module_bytes==43197 and module_lines==649
(a/'report-before-final.txt').write_bytes((a/'report.txt').read_bytes())
report=f'''CLEAR — selected-edge accepting coverage owner review

Final review time: {datetime.datetime.now().astimezone().isoformat()}
Source checkpoint: bcd40a836d8b1ae4d388fecf0f1ca81a27cbb673.

The primary SelectedEdge.complete_with_fragments_resources_accepting preserves the ENTIRE original SelectedEdgeResources admission and existential/result packet. Its bounds and structural witnesses precede the universal semantic observer. The literal original contract recovery is 4184 bytes, SHA256 845c61a06dbdcbdc1478adb3fa82b91ef5dea697138ef043af60c169da94f47e. Recovery removes only the final observer and reverses the theorem name. No original clause, result endpoint, resource forecast, protected-root field, Post or full final Memos was removed.

The primary proof calls actual EdgeInputs.complete once and TraversalCoverage once. Current Context annotations derive projected own equality and residual meaning. Fresh assignments preserve old bounded state constraints. Exact forward descent needs no ValidSuspended premise. Actual indexed child order is retained. Traversal acceptance forces the SAME actual result to complete. Actual finish_semantics records the residual with the native PCSGuard predicate at the SAME returned native heap/cache. The stopped structural packet is retained and a supplied accepted model contradicts its actual result equation. No Safe fact is derived from rejection.

The accepted_complete wrapper was also read in full. It takes genuine native edge acceptance, original Satisfies and all inherited Holds before choosing its operational bounds. It derives the successful actual projection and inherited arity, reserves only the original deterministic current projection, calls the primary producer once and retains its entire strengthened result under explicit grouping. The primary's model-independent bounds and the accepted wrapper's model-before-bounds scope remain distinct.

All five complete NEW public signature/axiom blocks were read, 37628 bytes over 475 lines. The full public readback is retained as evidence rather than claimed to have been reread in all historical detail: 630571 bytes, SHA256 77830f9982c262fde1d9c5afb8b82cb8f899d0aa0890ad976a4790b39226c0c1. Its entire previous 592943-byte prefix is literally equal. Root's validation records all 163 old blocks and 86 old source modules unchanged. Four installed modules contain 649 lines, 43197 bytes and five public theorems; no new definitions, predicates or data structures. All installed module bytes match the successful strict source snapshots. The only reported axiom dependencies are propext, Classical.choice and Quot.sound.

The final owned primary source is v3, 343 lines, 23689 bytes, SHA256 14396aa87af055f6081cfdd2f59461f061b2701ea7047c784b88415604a264c2. v1 was untested. v2's first actual strict check failed only an id reduction at the ordered mapping step; its full 1577-byte failure and source are retained. Root v3 adds only id_eq to the existing simpa-only list. Literal public statement equality and exact byte delta were checked. The authoritative second strict check passes with empty raw output. All successful module checks and standalone Audit use actual 4 GiB memory.max/high and zero swap, with warnings and all linters fatal. Aggregate Audit passes 4242 jobs and checks 80066 dependencies. Its replayed old dependency warning remains in the retained build output. No check was run by this worker.

Final prose was read in full: lean/notes-current-selected-coverage.md, 10380 bytes, SHA256 8ada69c850ab52921f5ff453ab20fa220e0b05da81adb2b544fe9eebac65d559. Each of the nine complete inserted status regions, including the extra FINDINGS handoff paragraph, was read. The eight ordinary regions are equal and FINDINGS starts with the same region. Every inverse removal was independently compared with the exact preserved prior document bytes. Cuts are labeled cuts with source/full hash and one-based inclusive line bounds; no partial copy is described as a whole document copy.

The strongest new claim is local symbolic selected-edge coverage under the declared native/current enum/resource admission. Native selection still must retain an accepting resident edge. Full recursive coverage, equivalent-language pruning callback coverage, frontier expansion, Discharged/rendering coverage, remaining public/native admission and full physical Haskell correspondence remain open. No Graph language substitutes for native semantics. There is no new Canonical, inherited validity, retention, universal Ranges, desired future success or final-assignment admission. H6 and the earlier conditional finite rendering soundness keep their exact previous scopes. No Haskell source, Cabal file, native test or benchmark changed or ran in this proof checkpoint. External KBO candidate integration and execution are not inferred from these proofs.

Publication condition: Root will create and verify the immutable archive only after this report and all live preflight checks pass. Portable frozen-byte and committed-byte verification must pass before publication. This review does not claim archive creation, committed verification or publication has happened.

Only /tmp/mcfta-selected-coverage-20261027/owner was written by this worker. Earlier frozen bundles and repository files were not modified. This owner bundle is sealed after this report. No further writes are permitted.
'''
(a/'report.txt').write_text(report)
(a/'final-prose-review.json').write_text(json.dumps({'status':'CLEAR','reviewed_at':datetime.datetime.now().astimezone().isoformat(),'source_head':'bcd40a836d8b1ae4d388fecf0f1ca81a27cbb673','whole_note':{'source':str(root/'lean/notes-current-selected-coverage.md'),**ident((root/'lean/notes-current-selected-coverage.md').read_bytes())},'inserted_regions_read':9,'all_inverse_bodies_literal_equal':True,'archive_committed_publication':'future; not asserted by this review'},indent=2)+'\n')
# Exclude ONLY the owner root pins and seal. Nested files, including any nested seal, remain payloads.
exclude={a/'pins.json',a/'FROZEN.json'}
files=sorted(p for p in a.rglob('*') if p.is_file() and p not in exclude)
entries=[{'path':str(p.relative_to(a)),**ident(p.read_bytes())} for p in files]
pins={'files':entries}
pinsb=(json.dumps(pins,indent=2)+'\n').encode();(a/'pins.json').write_bytes(pinsb)
seal={'status':'FROZEN','sealed_at':datetime.datetime.now().astimezone().isoformat(),'source_head':'bcd40a836d8b1ae4d388fecf0f1ca81a27cbb673','pins_sha256':hashlib.sha256(pinsb).hexdigest(),'payload_count':len(entries),'exact_file_count':len(entries)+2,'excluded_only':['pins.json','FROZEN.json'],'source_records':len(index['sources']),'literal_cuts':sum(len(r.get('cuts',[])) for r in index['sources']),'report_sha256':ident((a/'report.txt').read_bytes())['sha256']}
(a/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
# Verification below is read-only. Nothing is written after FROZEN.json.
actual={str(p.relative_to(a)) for p in a.rglob('*') if p.is_file()}
assert actual=={e['path'] for e in entries}|{'pins.json','FROZEN.json'}
assert len(actual)==seal['exact_file_count']
for e in entries:assert ident((a/e['path']).read_bytes())=={'bytes':e['bytes'],'sha256':e['sha256']}
assert hashlib.sha256((a/'pins.json').read_bytes()).hexdigest()==seal['pins_sha256']
print(json.dumps({'manifest':str(a/'pins.json'),'seal':str(a/'FROZEN.json'),**seal,'seal_sha256':ident((a/'FROZEN.json').read_bytes())['sha256']},indent=2))
