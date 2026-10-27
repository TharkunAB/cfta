from pathlib import Path
import json,hashlib,datetime
repo=Path('/home/tritlo/Code/mcfta')
out=Path(__file__).resolve().parent
specs='''
lean/MicroCFTA/SourceCurrentConjunctionEquality.lean|20-29,60-76
lean/MicroCFTA/SourceEqualityAnnotationHeap.lean|14-16,50-79
lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCompletion.lean|20-32,37-78
lean/MicroCFTA/SourceCurrentAllocatedPartialInvariant.lean|24-46,71-76
lean/MicroCFTA/SourceCurrentAllocatedNativeInventoryState.lean|24-53
lean/MicroCFTA/SourcePruningEnumerationRecursivePacket.lean|20-36
lean/MicroCFTA/SourceCurrentAllocatedNativeConstructedHistory.lean|24-54
lean/MicroCFTA/InternedNestedConstruction.lean|15-27
lean/MicroCFTA/InternedFreshOrdinaryConstruction.lean|99-136
lean/MicroCFTA/InternedFreshOrdinaryConstraintHeap.lean|15-45,84-172
lean/MicroCFTA/InternedFreshOrdinaryStoredConstraintHeap.lean|17-87
lean/MicroCFTA/InternedConstructorTemplates.lean|227-244
lean/MicroCFTA/InternedStoredSubstitution.lean|50-94
lean/MicroCFTA/InternedFreshOrdinaryStoredSubstitution.lean|75-86
lean/MicroCFTA/MergedFreshOrdinaryExposure.lean|18-50
lean/MicroCFTA/SourcePruningNativeView.lean|20-57,59-80
lean/MicroCFTA/SourceRecursiveIntersectionMaybeMu.lean|20-38,57-77
lean/MicroCFTA/SourceEqualityNativeDemand.lean|58-101
lean/MicroCFTA/SourceRecursiveIntersectionNative.lean|35-77
lean/MicroCFTA/SourceEqualityNativeCheckedCode.lean|22-32,75-99
lean/MicroCFTA/SourcePruningEnumerationCheckedWorkerArity.lean|20-58,59-100
lean/MicroCFTA/SourceCurrentAllocatedMkEdge.lean|35-47,50-81
lean/MicroCFTA/SourceCurrentAllocatedParentEdge.lean|75-102
lean/MicroCFTA/SourcePruningEnumerationHeadCheckedArity.lean|27-95
lean/MicroCFTA/SourcePruningEnumerationSetChildrenArity.lean|9-59
lean/MicroCFTA/InternedRecordCoherence.lean|13-35,64-115
lean/MicroCFTA/SourceCurrentAllocatedNativeCodeFields.lean|21-32,78-92,167-202
lean/MicroCFTA/SourcePruningEnumerationSelectedInvocationLanguage.lean|80-93
lean/MicroCFTA/SourcePruningEnumerationOwnArity.lean|1-93
lean/MicroCFTA/SourceEqualityMkEdgeArity.lean|14-45
lean/MicroCFTA/SourceEqualityMkEdgeAllocation.lean|20-62
lean/MicroCFTA/SourcePruningEnumerationConstraint.lean|5-43
cfta/src/Data/CFTA/Interned/Type.hs|390-400,553-568
cfta/src/Data/CFTA/Equality/Constraint.hs|321-331
'''
hash=lambda b:hashlib.sha256(b).hexdigest()
index=[]
for row in specs.strip().splitlines():
 rel,spans=row.split('|');p=repo/rel;b=p.read_bytes();lines=b.splitlines(keepends=True)
 copy='sources/'+rel;q=out/copy;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 rec={'source_path':str(p),'copy':copy,'bytes':len(b),'lines':len(lines),'sha256':hash(b),'review_scope':'Focused literal cuts; whole copy preserves source provenance.','cuts':[]}
 for span in spans.split(','):
  first,last=map(int,span.split('-'))
  if first<1 or last>len(lines):raise ValueError((rel,first,last,len(lines)))
  sliced=b''.join(lines[first-1:last]);dest='cuts/'+rel.replace('/','__')+f'-L{first}-L{last}.txt'
  target=out/dest;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(sliced)
  rec['cuts'].append({'path':dest,'first_line':first,'last_line':last,'bytes':len(sliced),'sha256':hash(sliced)})
 index.append(rec)
record={'scope':'Source-only independent origin propagation audit. No compiler, builds, tests, Git, network or repository writes.','captured_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':index,'whole_count':len(index),'cut_count':sum(len(r['cuts']) for r in index),'cut_lines':sum(c['last_line']-c['first_line']+1 for r in index for c in r['cuts'])}
(out/'source-pins.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['whole_count','cut_count','cut_lines']}))
