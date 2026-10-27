from pathlib import Path
import json,hashlib,difflib,datetime
area=Path('/tmp/mcfta-selected-coverage-20261027')
a=area/'owner'
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
v2=(a/'drafts/v2/SourcePruningEnumerationSelectedEdgeCoverage.lean').read_bytes()
v3=(a/'drafts/v3/SourcePruningEnumerationSelectedEdgeCoverage.lean').read_bytes()
assert v3==v2.replace(b'[descendScs, EqualityTrie.descendScs, List.map_append, List.filter_append]',b'[id_eq, descendScs, EqualityTrie.descendScs, List.map_append, List.filter_append]',1)
def stmt(b):
 s=b.decode();i=s.index('theorem complete_with_fragments_resources_accepting\n');return s[i:s.index(' := by',i)].encode()
assert stmt(v2)==stmt(v3)
comparison={'status':'PASS','checked_at':datetime.datetime.now().astimezone().isoformat(),'change':'One id_eq entry added to the existing simpa only lemma list. No statement or other proof change.','v2':ident(v2),'v3':ident(v3),'public_statement':ident(stmt(v3))}
(a/'v2-v3-exact-delta.json').write_text(json.dumps(comparison,indent=2)+'\n')
(a/'v2-v3.diff').write_text(''.join(difflib.unified_diff(v2.decode().splitlines(keepends=True),v3.decode().splitlines(keepends=True),fromfile='v2',tofile='v3')))
index=json.loads((a/'source-index.json').read_text())
sources=[]
for attempt in ['strict-selected-coverage-1','strict-selected-coverage-2']:
 report=json.loads((area/attempt/'report.json').read_text())
 raw=(area/attempt/'raw.log').read_bytes()
 source=area/attempt/'MicroCFTA/SourcePruningEnumerationSelectedEdgeCoverage.lean'
 sb=source.read_bytes()
 assert ident(raw)['sha256']==report['sha256'] and len(raw)==report['bytes']
 assert ident(sb)['sha256']==report['source_sha256']
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for p in [area/attempt/'report.json',area/attempt/'raw.log',source]:
  snap=Path('checks')/attempt/p.relative_to(area/attempt)
  (a/snap).parent.mkdir(parents=True,exist_ok=True);(a/snap).write_bytes(p.read_bytes())
  record={'source':str(p),'snapshot':str(snap),**ident(p.read_bytes()),'cuts':[]}
  if p==source:
   lines=sb.splitlines(keepends=True)
   for first,last in [(31,115),(212,226),(298,341)]:
    cut=b''.join(lines[first-1:last]);cp=Path('checks')/attempt/f'L{first}-L{last}.lean.txt';(a/cp).write_bytes(cut)
    record['cuts'].append({'snapshot':str(cp),'first_line':first,'last_line':last,**ident(cut),'source_sha256':record['sha256']})
  sources.append(record)
for p in [area/'selected-id-reduction-repair.json',a/'drafts/v3/SourcePruningEnumerationSelectedEdgeCoverage.lean']:
 snap=Path('checks')/('root-repair.json' if p.suffix=='.json' else 'final-v3.lean')
 (a/snap).write_bytes(p.read_bytes());sources.append({'source':str(p),'snapshot':str(snap),**ident(p.read_bytes()),'cuts':[]})
index['sources'].extend(sources)
(a/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
initial=a/'report-initial.txt'
if not initial.exists():initial.write_bytes((a/'report.txt').read_bytes())
report=(a/'report.txt').read_text().replace('Status: OPEN. Draft v2 is UNTESTED. Root owns all compiler, build, source installation and publication actions. No compiler or native test was run by this worker.', 'Status: OPEN. Final v3 is checked by Root: strict-selected-coverage-2 PASS, exit 0, raw output 0 bytes, actual memory.max=memory.high=4294967296 and memory.swap.max=0. Root owns all compiler, build, source installation and publication actions. No compiler or native test was run by this worker. Initial report bytes remain in report-initial.txt.')
report+='''\nAuthoritative strict attempts\nThe first actual strict check compiled v2 b57dae435721228b55fe4fc456991252a2dd41b0da3a75bfe52d3156cd21dfd9 and failed only the local ordered-map id reduction. Its full 1577-byte output has SHA256 f9bfd94702a1bd4a4e3d5054ed87c1f6819bb70ebbb187a0032a387f1c246a69. Root v3 adds only id_eq to the existing simpa-only list. Exact delta and literal public-statement equality are checked in v2-v3-exact-delta.json. Final v3 is 343 lines, 23689 bytes, SHA256 14396aa87af055f6081cfdd2f59461f061b2701ea7047c784b88415604a264c2. strict-selected-coverage-2 is the authoritative successful check. Both attempt sources, reports and raw logs are copied exactly under checks/. v1 was not tested. Installed build, final public readback and prose review remain pending.\n'''
(a/'report.txt').write_text(report)
print(json.dumps({'strict_final':'PASS','sources':len(index['sources']),'cuts':sum(len(x['cuts']) for x in index['sources']),'final':ident(v3)},indent=2))
