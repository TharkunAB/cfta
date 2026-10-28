from pathlib import Path
import hashlib,json,re
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-native-partial-output-20261028');O=B/'program-origin-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,v):return put(p,(json.dumps(v,indent=2)+'\n').encode())
records=[]
def add(p,spans,scope,dest=None):
 p=Path(p);b=p.read_bytes();ls=b.splitlines(keepends=True)
 rel=p.relative_to(R) if p.is_relative_to(R) else Path('stage')/p.relative_to(B)
 rec={'source':str(p),'whole':put(dest or O/'sources'/rel,b),'cuts':[],'reviewed_scope':scope}
 for first,last in spans:
  assert 1<=first<=last<=len(ls),(p,first,last,len(ls))
  c=put(O/'cuts'/rel/(str(first)+'-'+str(last)+'.txt'),b''.join(ls[first-1:last]));c.update(first_line=first,last_line=last);rec['cuts'].append(c)
 records.append(rec);return b
L=R/'lean/MicroCFTA'
add(L/'SourcePruningProgramHoleOrigins.lean',[(14,71),(73,79)],'WHOLE final Root proof-only repair read, both public declarations compared to owner v1. Actual strict1 failure and strict2 PASS read in full. Actual build141 PASS receipt read. Literal actual programHoles and ProgramAt; no runtime evaluator or predicate added.')
add(L/'SourcePruningProgramTypeOriginBoundary.lean',[(16,44)],'WHOLE owner v1 and final Root v2 read; public proposition identical. Actual failure1 and PASS2 source/raw/report read. This is a pure provenance-insufficiency witness, not a native/public Haskell execution or a Packet/reachability theorem.')
add(L/'SourcePruningPositions.lean',[(18,50),(91,123),(126,163)],'WHOLE positions source read. Literal programHoles/typePositions and their constructor/member laws supply the actual operational position classification. No native IntSet extraction claim.')
add(L/'SourcePruningProgramSemantics.lean',[(17,37),(39,55),(122,138)],'WHOLE program-position semantics source read. ProgramAt omits annotation/marker positions and gives no reflexive constant/filter root position. programs_complete and startMatches_refutes give genuine prior semantic bridges.')
add(L/'SourcePruningProgramEncodingHereditary.lean',[(13,42)],'WHOLE existing encoding hereditary source read. It requires actual ProgramAt; it is not duplicated.')
add(L/'SourcePruningProgramAvoidanceHereditary.lean',[(14,32)],'WHOLE existing avoidance hereditary source read. ProgramAt.trans composes actual positions; Avoids.at_program transfers original avoidance.')
add(L/'SourcePruningStructuralTemplateMeaning.lean',[(5,25)],'Only source-grammar commentary and complete ProgramEncoding declaration reread. Annotation term is unrestricted. Whole source is preserved as identity, not a renewed reading of its old conversion proof.')
add(L/'Fragments.lean',[(25,40)],'Fragment constructors and literal fill/rename operations read. Remaining generic intersection/heap proofs were not reread for this bounded task.')
add(L/'SourcePruningRecordTypes.lean',[(19,55),(70,80),(87,104)],'Metadata fields, real type update/callback, stopping test and metadata receipt read. No runtime of this file was changed. Other old callback proofs not reread.')
add(L/'SourcePruningEnumerationChildCoverage.lean',[(90,144),(178,201)],'WHOLE actual child coverage source read. A fresh child uses actual concrete term assignment and exact raw singleton; original variables agree. Terminal rows retain the assignment. This does not itself classify source program/type positions.')
add(L/'SourcePruningEnumerationSelectedEdgeCoverage.lean',[(192,238),(307,342)],'Model construction and final accepting/rejected branches read. Exact ordered child fills and original-variable agreement are available. No full reread of every resource induction field is claimed.')
add(L/'SourcePruningEnumerationNativeIndex.lean',[(17,30)],'Native candidate definition and surrounding index write/completion source read. Missing graph handle is never an expandable candidate. Most count proof details are identity-only.')
add(L/'SourcePruningEnumerationCachedOwn.lean',[(14,50),(52,82)],'WHOLE cached own-prefix source read. Own-class allocation uses none handles and preserves exact child order/buckets; none slots are excluded by the native candidate definition.')
add(L/'SourcePruningEnumerationEdgeInputs.lean',[(16,20),(23,78)],'WHOLE EdgeInputs source read. Actual inherited/own child descent and closed-available/resource receipts were inspected. These structural receipts do not carry source-language positions.')
add('specftacular/src/Specftacular/Pruning.hs' if False else R/'specftacular/src/Specftacular/Pruning.hs',[(47,58),(97,141),(143,175)],'Only full cited public contract, actual callback/narrowing, programHoles and typePositions regions read. No full-module runtime or Haskell execution claim.')
add(R/'specftacular/src/Specftacular.hs',[(1229,1234)],'Only the actual canPrune signature guard and its immediate explanation reread. Its type-to-native-language bridge is not proved here.')
# Public declarations must be byte-identical across proof-only repairs.
comparisons=[]
for module,old,new in [
 ('SourcePruningProgramHoleOrigins',O/'drafts/v1/SourcePruningProgramHoleOrigins.lean',L/'SourcePruningProgramHoleOrigins.lean'),
 ('SourcePruningProgramTypeOriginBoundary',O/'type-boundary/drafts/v1/SourcePruningProgramTypeOriginBoundary.lean',L/'SourcePruningProgramTypeOriginBoundary.lean')]:
 def headers(p):
  text=p.read_text();return [(m.group(1),text[m.start():].split(':= by',1)[0].rstrip()) for m in re.finditer(r'^theorem ([^\s]+)',text,re.M)]
 a=headers(old);n=headers(new);assert a==n
 for name,header in a:
  rec=put(O/'contracts'/module/(name+'.txt'),header.encode());comparisons.append({'module':module,'theorem':name,'bytes':rec['bytes'],'sha256':rec['sha256'],'proof_only_repair':True,'public_statement_byte_identical':True})
for name in ['program-hole-origins-strict-1','program-hole-origins-strict-2','type-origin-boundary-strict-1','type-origin-boundary-strict-2','program-origin-build-1']:
 p=B/name;r=json.loads((p/'report.json').read_text());raw=(p/'raw.log').read_bytes()
 assert len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if 'source_sha256' in r:assert sha(Path(r['command'][-1]).read_bytes())==r['source_sha256']
 for f in sorted(p.rglob('*')):
  if f.is_file() and f.suffix in {'.lean','.json','.log','.txt'}:add(f,[],'Actual Root checked source/report/raw retained. Hash/exit/measured limits verified. These are Root commands, not reviewer compilers.',O/'checks'/name/f.relative_to(p))
for name in ['v1-program-hole-reductions','v2-type-origin-elimination']:
 for p in sorted((B/'root-drafts'/name).rglob('*')):
  if p.is_file():add(p,[],'Immutable actual Root proof-only repair and delta; reviewed in full.',O/'lineage'/name/p.relative_to(B/'root-drafts'/name))
dump(O/'contract-comparisons.json',comparisons)
dump(O/'source-index.json',{'sources':records})
dump(O/'status-current.json',{'status':'OPEN; two final sources strictPASS and program-hole buildPASS. Stage integration/public/docs pending.','new_theorems':3,'no_new_runtime_definition_or_predicate':True,'source_identities':len(records),'literal_cuts':sum(len(x['cuts']) for x in records),'reviewer_no_compiler_build_native_Git_network_board_or_repository_write':True})
print(json.dumps({'sources':len(records),'cuts':sum(len(x['cuts']) for x in records),'declaration_comparisons':len(comparisons)},indent=2))
