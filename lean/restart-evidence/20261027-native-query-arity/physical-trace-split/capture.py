from pathlib import Path
import json,hashlib,datetime
R=Path('/tmp/mcfta-native-query-arity-20261027/physical-trace-split');P=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
assert not (R/'FROZEN').exists()
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def js(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
idx={'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); original LF retained','sources':[]}
def add(p,cuts,scope,dest):
 b=p.read_bytes();q=R/dest;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 rec={'source':str(p),'snapshot':str(q),**ident(b),'scope':'whole identity; semantic read scope stated separately','reviewed_scope':scope,'cuts':[]}
 for a,z,purpose in cuts:
  assert 1<=a<=z<=len(b.splitlines())
  c=b''.join(b.splitlines(keepends=True)[a-1:z]);out=R/'literal-cuts'/f'{p.stem}-{a}-{z}.txt';out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(c)
  rec['cuts'].append({'first_line':a,'last_line':z,'snapshot':str(out),**ident(c),'scope':'literal cut','purpose':purpose})
 idx['sources'].append(rec)
add(R/'drafts/v1/SourcePruningEnumerationNativeBodyTrace.lean',[(28,72,'rich child count and range-free cons split'),(74,121,'exact actual walk-work and first body inversion'),(123,209,'whole actual branch observer')],'WHOLE209line source-only self-review; UNCOMPILED','proposal-snapshots/v1.lean')
inputs={
 'SourceCurrentAllocatedNativeSemanticTraceReadback':([(25,51,'existing checked Inputs/Fields inversion'),(89,135,'existing exact rich bind inverse; no range/Good premise'),(137,156,'existing actual rich Trace effects from original Good/Fields'),(176,216,'existing rich ordered Walk and extraction'),(218,266,'older range-bearing cons/work consumers, now used only as proof pattern')],'Focused listed declarations read; entire original identity retained'),
 'SourceCurrentAllocatedNativePhysicalTraceCompletion':([(31,54,'existing rich Trace stores actual physical Inputs and composes'),(68,78,'existing rich bind forward transport'),(91,110,'rich receipt one-way erasure; no reverse rawdone claim')],'Focused actual Trace/composition/Receipt declarations read'),
 'SourcePruningEnumerationNativeBodyOriginArity':([(26,77,'actual first instruction derives sentinel or ready branch'),(79,158,'previous row-only origin theorem uses raw accepted Walk')],'WHOLE final installed source read'),
 'SourceEqualityNativeCheckedCode':([(23,34,'literal accepted children code and sentinel constructor')],'Focused runtime control flow and actual child compile shape read'),
 'SourceCurrentAllocatedNativePhysicalCompletion':([(27,35,'initial Good contains current physical/field facts'),(129,148,'actual step invariants retain Good/Fields')],'Focused source Good/step theorem read; no final Good supplied'),
 'SourceCurrentAllocatedNativePhysicalExecution':([(44,65,'rich Inputs retain actual current operands and KeySafe checks')],'Focused actual Inputs definition read; no claim numeric checks disappear'),
 'SourceEqualityNativeDemandBodyYield':([(20,69,'existing actual pure body control inversion')],'WHOLE source read'),
 'SourceEqualityNativeDemandControl':([(72,85,'real ready body gives exact operation-state endpoint')],'Focused actual source ready receipt read'),
 'SourceEqualityNativeDemandTraceSplit':([(41,78,'older raw bind inverse is only comparison; no checked Inputs restoration from raw trace')],'WHOLE raw source read')}
for m,(cuts,scope) in inputs.items():
 p=P/f'{m}.lean';ls=len(p.read_bytes().splitlines());cuts=[(a,min(z,ls),s) for a,z,s in cuts];add(p,cuts,scope,f'whole-inputs/{m}.lean')
js(R/'source-index.json',idx)
js(R/'OPEN.json',{'status':'UNCOMPILED v1; root serial strict check pending','recorded_at':datetime.datetime.now().astimezone().isoformat(),'draft':str(R/'drafts/v1/SourcePruningEnumerationNativeBodyTrace.lean'),'draft_identity':ident((R/'drafts/v1/SourcePruningEnumerationNativeBodyTrace.lean').read_bytes()),'source_records':len(idx['sources']),'literal_cuts':sum(len(r['cuts']) for r in idx['sources'])})
print(json.dumps({'sources':len(idx['sources']),'cuts':sum(len(r['cuts']) for r in idx['sources']),'state':'OPEN / UNCOMPILED'},indent=2))
