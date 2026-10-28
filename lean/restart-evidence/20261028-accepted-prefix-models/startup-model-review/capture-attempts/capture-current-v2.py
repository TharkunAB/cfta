from pathlib import Path
import json,hashlib,difflib
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-accepted-prefix-20261028');O=B/'startup-model-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,o):return put(p,(json.dumps(o,indent=2)+'\n').encode())
records={}
if (O/'source-index.json').exists():records={z['source']:z for z in json.loads((O/'source-index.json').read_text())['sources']}
def add(rel,spans,scope):
 p=R/rel;b=p.read_bytes();ls=b.splitlines(keepends=True);rec={'source':str(p),'whole':put(O/'sources'/rel,b),'cuts':[],'reviewed_scope':scope}
 for first,last in spans:
  assert 1<=first<=last<=len(ls),(rel,first,last,len(ls))
  c=put(O/'cuts'/rel/(str(first)+'-'+str(last)+'.txt'),b''.join(ls[first-1:last]));c.update(first_line=first,last_line=last);rec['cuts'].append(c)
 records[str(p)]=rec
L='lean/MicroCFTA/'
add(L+'SourcePruningEnumerationInitialModel.lean',[(30,59),(60,77)],'WHOLE immutable owner v1 and installed exact source read. Actual strict1 PASS empty; no added admission or operational definition.')
add(L+'SourcePruningEnumerationAcceptedHeadModels.lean',[(250,284),(285,309)],'WHOLE final Root 311-line module read. Original packet declaration compared in full. Actual callback Frame transports the head model to the same framed restart cache; no emitted-output claim.')
add(L+'SourcePruningEnumerationInitialCarriers.lean',[(27,47),(48,54)],'WHOLE original startup carrier source read. Entire original declaration recovered from the new model theorem.')
add(L+'SourcePruningEnumerationInitialPacket.lean',[(29,53),(54,88)],'WHOLE original initial Packet source read. Its actual literal initial cache, handle and indices remain unchanged.')
add(L+'SourcePruningEnumerationNativeLanguage.lean',[(22,40),(107,124)],'WHOLE native language source read. handles_lookup supplies exact original root meaning; satisfies_frame is the actual Root model-transport leaf.')
add(L+'EnumerationCorrectness.lean',[(136,146),(242,249)],'Read initial_semantics, Satisfies and nearby allocation/suspended semantics; whole source preserved as identity, not a whole-proof-body reading claim.')
add(L+'SourcePruningResumeRefutation.lean',[(36,40)],'Refutes definition and instance scope read. Other refutation proofs are preserved as identity, not used in this startup proof.')
add(L+'SourcePruningProgramSemantics.lean',[(17,37)],'WHOLE ProgramSemantics source read. ProgramAt, Avoids and actual partial-program completion were inspected; generic native-origin transport is not supplied by this file.')
add(L+'SourcePruningProgramEncodingHereditary.lean',[(13,49)],'WHOLE existing encoding hereditary theorem and proof read. It requires original ProgramEncoding and actual ProgramAt.')
add(L+'SourcePruningStructuralTemplateMeaning.lean',[(1,26)],'Only source-grammar documentation and full ProgramEncoding declaration read in this task. The old 245-line conversion proof is not claimed reread.')
add(L+'InternedGuardedLanguage.lean',[(23,48)],'Independent native meaning, edgeMeaning and forest definitions read, plus monotonicity/constructor observer region. No source grammar or forbidden-template avoidance is present in these clauses.')
add(L+'Template.lean',[(15,21),(68,82)],'Pattern constructors, child alignment, Matches and hole_matches read. Remaining graph restriction proofs not used or reviewed.')
add(L+'SourcePruningEnumerationAcceptedHeadCallback.lean',[(43,249)],'ENTIRE previous callback-policy declaration read by exact comparison. Its other proof body is preserved as identity, not reread in this task.')
add('cfta/src/Data/CFTA/Enumeration.hs',[(297,314)],'Literal public native startup read. Other Haskell enumeration paths not reviewed or executed.')
add('specftacular/src/Specftacular/Pruning.hs',[(47,58),(95,141),(328,343)],'Only cited public contract/typed callback and narrow/structural-template regions read; no whole-module or runtime execution claim.')
add('specftacular/src/Specftacular/Utils.hs',[(34,39),(54,56),(89,103)],'Fixed arrow marker, filter wrapper, mapp and nearby source-grammar construction documentation read; no whole-module proof claimed.')
add('specftacular/src/Specftacular/Rewriting.hs',[(326,367)],'Actual pruningTemplates rule selection and rawTemplate source region read. Other rewriting/order implementation not reviewed in this task.')
add('specftacular/src/Specftacular.hs',[(1229,1234),(1281,1284),(1303,1307)],'Only actual canPrune definition and both template-enable branches read. No whole public pipeline correctness or semantic origin proved.')
# Recover every literal old input, witness and output field of the Root callback wrapper.
a=(R/L/'SourcePruningEnumerationAcceptedHeadCallback.lean').read_text();n=(R/L/'SourcePruningEnumerationAcceptedHeadModels.lean').read_text()
a=a[a.index('theorem head_finite_complete_resources_callback_policy'):].split(':= by',1)[0].rstrip();n=n[n.index('theorem head_finite_complete_resources_callback_models'):].split(':= by',1)[0].rstrip();i=n.rfind('\n          ∀ (ambient : InternedGuardedLanguage.Env Symbol)');assert i>=0
part=n[:i].rstrip();assert part.endswith(') ∧');part=part[:-3]+'\n      | _ => True';part=part.replace('theorem head_finite_complete_resources_callback_models','theorem head_finite_complete_resources_callback_policy',1).replace('            ((((Packet','            (((Packet',1);assert part==a
assert len(a.encode())==16289
put(O/'root-review/entire-original-callback-declaration.txt',a.encode());put(O/'root-review/recovered-original-callback-declaration.txt',part.encode());dump(O/'root-review/callback-contract-comparison.json',{'status':'pass','scope':'Entire original theorem declaration, including theorem name, all binders/witnesses/old fields. Trailing pre-proof whitespace trimmed. Only new theorem name, one old-result grouping and appended semantic observer removed.','bytes':len(a.encode()),'sha256':sha(a.encode()),'byte_identical':True,'new_input_admission':False,'old_producer_calls':(R/L/'SourcePruningEnumerationAcceptedHeadModels.lean').read_text().split(':= by',1)[1].count('head_finite_complete_resources_callback_policy ')})
for name in ['initial-model-strict-1','accepted-head-models-strict-1']:
 d=B/name;r=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();assert r['exit_code']==0 and len(raw)==r['bytes']==0 and sha(raw)==r['sha256']
 source=Path(r['command'][-1]);assert sha(source.read_bytes())==r['source_sha256']
 for p in sorted(d.rglob('*')):
  if p.is_file() and p.suffix in {'.lean','.json','.log','.txt'}:put(O/'checks'/name/p.relative_to(d),p.read_bytes())
dump(O/'source-index.json',{'sources':list(records.values())})
dump(O/'status-current.json',{'status':'OPEN; startup model and Root callback model strict1 PASS exact. Program avoidance helper pending Root check. Public/docs pending.','source_identities':len(records),'literal_cuts':sum(len(r['cuts']) for r in records.values()),'owner_startup_sha256':sha((R/L/'SourcePruningEnumerationInitialModel.lean').read_bytes()),'root_callback_sha256':sha((R/L/'SourcePruningEnumerationAcceptedHeadModels.lean').read_bytes()),'no_reviewer_compiler_build_Git_native_network_or_repository_write':True})
print(json.dumps({'sources':len(records),'cuts':sum(len(r['cuts']) for r in records.values()),'old_callback_bytes':len(a.encode()),'old_callback_sha256':sha(a.encode())},indent=2))
