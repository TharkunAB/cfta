from pathlib import Path
import hashlib,json,datetime
repo=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-recursive-history-20261027/semantic-gates-review')
sha=lambda b:hashlib.sha256(b).hexdigest()
primary=[
('lean/MicroCFTA/SourcePruningEnumerationPrefixCanonical.lean',[(13,38)]),
('lean/MicroCFTA/SourcePruningEnumerationNativeBranchCanonical.lean',[(33,64),(181,226)]),
('lean/MicroCFTA/SourcePruningEnumerationRecursiveCallbackCanonical.lean',[(35,57)]),
('lean/MicroCFTA/SourcePruningEnumerationEdgeChildLanguage.lean',[(18,32),(39,58),(90,123)]),
('lean/MicroCFTA/SourcePruningEnumerationEdgeInputs.lean',[(15,19),(25,70)]),
('lean/MicroCFTA/SourcePruningEnumerationRecursivePacket.lean',[(21,40),(43,61),(63,77)]),
('lean/MicroCFTA/SourcePruningEnumerationSelectedStep.lean',[(43,103)]),
('lean/MicroCFTA/SourcePruningEnumerationCheckedBuildArity.lean',[(18,49)]),
('lean/MicroCFTA/SourcePruningEnumerationCheckedWorkerArity.lean',[(23,53),(93,112)]),
('cfta/src/Data/CFTA/Enumeration.hs',[(268,293),(391,404),(469,474),(715,747),(756,773),(793,801),(993,1005),(1195,1207)])]
focused=[
('lean/MicroCFTA/EnumerationValidity.lean',[(18,60),(191,205)]),
('lean/MicroCFTA/SourcePruningEnumerationRecursion.lean',[(17,31)]),
('lean/MicroCFTA/SourcePruningEnumerationSelectedStepCompletion.lean',[(32,80)]),
('lean/MicroCFTA/SourcePruningEnumerationAction.lean',[(18,47)]),
('lean/MicroCFTA/SourcePruningEnumerationShallowChild.lean',[(20,40),(43,72)]),
('lean/MicroCFTA/SourcePruningEnumerationCachedPrepareCanonical.lean',[(18,65)]),
('lean/MicroCFTA/SourcePruningEnumerationParkedLanguage.lean',[(68,79)]),
('lean/MicroCFTA/SourceFlatPruningRecursionMeaning.lean',[(35,64)]),
('lean/MicroCFTA/SourcePruningEnumerationOrdinarySemanticGates.lean',[(26,46)]),
('cfta/src/Data/CFTA/Interned/Type.hs',[(554,568),(679,698)])]
sources=[];cuts=[]
for full,items in [(True,primary),(False,focused)]:
 for path,spans in items:
  raw=(repo/path).read_bytes(); lines=raw.splitlines(keepends=True)
  record={'path':str(repo/path),'source':str(repo/path),'bytes':len(raw),'sha256':sha(raw),
   'role':'designated source' if full else 'focused proof dependency',
   'read_scope':'listed cuts and relevant surrounding proofs only; snapshot is identity evidence, not an import-closure review'}
  if full:
   snapshot=Path('inputs')/path;(area/snapshot).parent.mkdir(parents=True,exist_ok=True);(area/snapshot).write_bytes(raw);record['snapshot']=str(snapshot)
  sources.append(record)
  for start,end in spans:
   assert 1<=start<=end<=len(lines),(path,start,end,len(lines))
   data=b''.join(lines[start-1:end]); dest=Path('cuts')/(Path(path).stem+f'--{start}-{end}'+Path(path).suffix)
   (area/dest).parent.mkdir(parents=True,exist_ok=True);(area/dest).write_bytes(data)
   cuts.append({'path':str(repo/path),'source':str(repo/path),'snapshot':str(dest),'start':start,'end':end,
    'source_sha256':sha(raw),'bytes':len(data),'sha256':sha(data)})
index={'version':1,'status':'FINAL SOURCE-ONLY ASSESSMENT; PROOFS UNBUILT','observed_at':datetime.datetime.now().astimezone().isoformat(),
 'sources':sources,'cuts':cuts,'whole_count':len(primary),'source_count':len(sources),'cut_count':len(cuts),
 'cut_lines':sum(c['end']-c['start']+1 for c in cuts),'read_scope':'report.txt; literal designated source cuts; source-only unexecuted drafts',
 'unreviewed_import_dependencies':['SourcePruningEnumerationOuter','SourcePruningEnumerationNativeGrowth','EnumerationPendingReplacement','SourceCurrentAllocatedPartialInvariant','SourceEqualityNativeCheckedCode full implementation','full semantic/native machine history outside the listed slices'],
 'drafts':[{'path':str(p.relative_to(area)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes()),'status':'UNBUILT; no validation claim'} for p in sorted((area/'drafts').iterdir())]}
(area/'source-pins.json').write_text(json.dumps(index,indent=2)+'\n')
# Verify literal source copies and cuts once as data operations.
for s in sources:
 assert sha(Path(s['source']).read_bytes())==s['sha256']
 if 'snapshot'in s:assert (area/s['snapshot']).read_bytes()==Path(s['source']).read_bytes()
for c in cuts:
 assert (area/c['snapshot']).read_bytes()==b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']])
payloads=[p for p in sorted(area.rglob('*')) if p.is_file() and p.name not in ['pins.json','FROZEN.json']]
pins={'version':1,'pins':[{'path':str(p.relative_to(area)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in payloads]}
pinraw=(json.dumps(pins,indent=2)+'\n').encode();(area/'pins.json').write_bytes(pinraw)
freeze={'status':'FROZEN SOURCE/DATA ONLY','pins_count':len(payloads),'pins_bytes':len(pinraw),'pins_sha256':sha(pinraw),
 'source_count':len(sources),'whole_count':len(primary),'cut_count':len(cuts),'cut_lines':index['cut_lines'],
 'proof_status':'All new drafts unbuilt. No Lean/native checks executed.', 'report_sha256':sha((area/'report.txt').read_bytes()),'source_pins_sha256':sha((area/'source-pins.json').read_bytes())}
(area/'FROZEN.json').write_text(json.dumps(freeze,indent=2)+'\n')
print(json.dumps(freeze,indent=2));print('FROZEN SHA256',sha((area/'FROZEN.json').read_bytes()))
