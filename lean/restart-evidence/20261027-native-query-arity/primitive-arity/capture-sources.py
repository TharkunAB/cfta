from pathlib import Path
import hashlib,json,datetime
repo=Path('/home/tritlo/Code/mcfta');out=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
specs=[('lean/MicroCFTA/SourcePruningEnumerationArityOrigins.lean',[(26,43),(70,132),(258,332)]),('lean/MicroCFTA/SourceRecursiveIntersectionMaybeMu.lean',[(20,76)]),('lean/MicroCFTA/InternedConstructorTemplates.lean',[(91,136)]),('lean/MicroCFTA/SourceEqualityNativeDemand.lean',[(48,56),(86,104)]),('lean/MicroCFTA/SourceRecursiveIntersectionNative.lean',[(29,53)]),('lean/MicroCFTA/InternedRecordCoherence.lean',[(64,76)]),('lean/MicroCFTA/SourceCurrentAllocatedNativeCodeFields.lean',[(197,207)])]
records=[]
for rel,spans in specs:
 p=repo/rel;b=p.read_bytes();lines=b.splitlines(keepends=True);copy='sources/'+rel
 dest=out/copy;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 rec={'source_path':str(p),'copy':copy,'bytes':len(b),'lines':len(lines),'sha256':h(b),'review_scope':'Focused literal cuts. Whole copy preserves provenance.','cuts':[]}
 for first,last in spans:
  assert last<=len(lines),(rel,last,len(lines))
  part=b''.join(lines[first-1:last]);path='cuts/'+rel.replace('/','__')+f'-L{first}-L{last}.txt';dest=out/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(part)
  rec['cuts'].append({'path':path,'first_line':first,'last_line':last,'bytes':len(part),'sha256':h(part)})
 records.append(rec)
index={'scope':'Actual native work and optional-binder primitive proof inputs. No broad native query/body inversion reviewed.','captured_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':records,'whole_count':len(records),'cut_count':sum(len(r['cuts']) for r in records),'cut_lines':sum(c['last_line']-c['first_line']+1 for r in records for c in r['cuts'])}
(out/'source-pins.json').write_text(json.dumps(index,indent=2)+'\n')
print(json.dumps({k:index[k] for k in ['whole_count','cut_count','cut_lines']}))
