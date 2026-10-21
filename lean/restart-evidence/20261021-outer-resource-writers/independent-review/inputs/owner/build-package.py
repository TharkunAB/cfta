from pathlib import Path
import hashlib,json,re,shutil
root=Path('/home/tritlo/Code/mcfta');here=Path('/tmp/mcfta-outer-resource-writers-proof');prefix='outer-resource-writers-'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
source=here/'SourceCurrentOuterResourceWriters.lean';text=source.read_text();head='MicroCFTA.SourceCurrentOuterResourceWriters.reached'
assert sha(source)=='50ae9ee05230de797cfe71b68c0fb016b4352f763c99161b98708fb9d20ceab5'
plan=Path('/tmp/mcfta-outer-resource-writers-next-plan')
shutil.copytree(plan,here/'inputs/plan')
pins=[]
for old in json.loads((plan/'plan-source-pins.json').read_text())['files']:
    pins.append({**old,'snapshot':'inputs/plan/inputs/root/'+old['path']})
pins.append({'path':'lean/MicroCFTA/'+source.name,'snapshot':source.name,'bytes':source.stat().st_size,'sha256':sha(source),'reviewed_ranges':[{'start':1,'end':len(text.splitlines()),'sha256':sha(source)}]})
write(here/(prefix+'source-pins.json'),{'schema':1,'files':pins})
ledger=[]
for stem in [prefix+'direct-1',prefix+'direct-2',prefix+'public-1']:
    receipt=json.loads((here/(stem+'.json')).read_text());log=here/(stem+'.log')
    ledger.append({'name':stem,'kind':'lean','lean_launched':True,'exit_code':receipt['exit_code'],'warning_diagnostics':len(re.findall(r'\bwarning(?:\([^)]*\))?:',log.read_text())),'receipt_sha256':sha(here/(stem+'.json')),'log_sha256':sha(log)})
write(here/(prefix+'attempt-ledger.json'),{'schema':1,'attempts':ledger,'prelaunch_proof_commands':0,'infrastructure_attempts':0})
public=here/(prefix+'public-1.log')
selection={'schema':1,'finalized':True,'source':source.name,'source_sha256':sha(source),'source_lines':len(text.splitlines()),'public_heads':[head],'selected_strict':prefix+'direct-2','selected_public':prefix+'public-1','lean_jobs':3,'failed_checks':1,'warning_checks':0,'infrastructure_attempts':0,'canonical_jobs':0,'new_public_pairs':1,'constructed_pairs':0,'public_headers_match_frozen_proposal':True,'prelaunch_proof_commands':0,'public_log_bytes':public.stat().st_size,'public_log_sha256':sha(public),'axioms_by_head':{head:['Classical.choice','Quot.sound','propext']},'official_edits_by_author':False,'initial_prelaunch_sha256':'66e1a8f75944c2c34cc4c6007f63a61efd450979aa15bc633c902623a256484f','actual_failed_source_sha256':'e4e88ee9d08656f1eb92151de30e31d4f01634a20e950ed8dba719e54d3eaaf9','source_repairs':'Prelaunch explicit request annotation. After strict1, explicit same request/before in walk endpoints and prefix heads plus two definitional Origins middle goals. No public header, entry resource, result or actual call changes.'}
write(here/(prefix+'selection.json'),selection)
(here/(prefix+'review.md')).write_text('''# Resource writers through unfinished outer prefixes

The selected 465-line module proves one public theorem, SourceCurrentOuterResourceWriters.reached. Its header is exactly the frozen proposal. It preserves the new resource-backed Origins at the last literal outer phase. It returns no duplicate resource tuple, public completed-node wrapper, or selected-owner theorem.

The theorem uses the same supplied ExecutionAncestry.Reached proof. Genuine initial Context, Frame, Fits, Carrier, phase Inputs, forecast Room, UnionNormal, native positive Support, causal History, conditional Merge storage, positive Merge storage, and initial Origins remain explicit. Initial Origins has the checked empty-table initializer and local edge-call producer. Already certified warm caller tables are allowed.

The private six-phase induction proves only edge-ledger preservation. Node publication and finish change the node table. Operations, Mu reconstruction, and raw rebuilds preserve edgeResults literally. Their ledger cases need no new physical, semantic, normality, NoNewMu, or position proof. The actual Mu outcome is still split, so successful return is not inferred from syntax.

The repeated head_edge helper calls the local ResourceParentWriters.edge_call on the same actual head. It retains ONE old OuterEdgeGuardAlphabet numeric receipt for that head and passes that receipt to OuterNativeStores.edge_call. It copies none of their resource, store, or lifecycle inductions. The actual local writer certificate contains one complete historical caller/resource tuple. Warm request equality uses that existing local producer; no current reader supplies historical writer resources.

Rows use the parent seed, then the descendant seed, then the original suffix. Walks use the literal indexed descent and its actual node return, then increment the index and use the node-return seed for the original suffix. Existing OuterInitialActual and OuterNativeStores endpoints supply resources and five stores at those exact completed sibling returns. No per-sibling Ready or supplied output law is used.

The eight prefix cases use only their actual constructor equations. Each snoc obtains one common resource/store tuple by calling OuterPrefixNativeStores.reached on the same earlier proof. The ledger induction hypothesis refers to exactly that middle caller. rows_edge needs only the completed head; rows_tail uses the completed head and descendants; walk_tail uses the completed earlier node. None requires a later enclosing completion. Other cases preserve the edge table literally.

Root and an independent reviewer read the complete 461-line draft before any proof launch. Root requested one explicit private request annotation. The original source and exact zero-job prelaunch patch are retained. Strict1 failed on six request/state inference errors. The exact repair fixes the actual request/before caller in two walk endpoints and two prefix heads. It also makes the literal unchanged edge table explicit with change Origins ... middle before two ledger IH applications. Root and the independent reviewer read the complete raw log and patch before strict2. No public premise, result, schedule, actual call or witness changed.

Selected strict2 is terminal 0 with a literal empty raw log. Selected public1 is terminal 0. Its complete FULL log has 451700 bytes and SHA256 35de5b5d0df2818ec9c897e018799e56d32e452850bd13cbdfbaaf4dbc450190. The printer begins with the exact final production bytes and has all eight required settings. Check/print public types agree. The public type contains no private Stores or phase predicates. No omission or diagnostic is present. The actual axiom set is exactly propext, Classical.choice and Quot.sound.

There are three owned Lean commands: failed strict1, clean strict2, and clean public1. There are no warning-bearing, infrastructure or canonical commands and no constructed example. Every attempt retains its exact input, raw log, receipt, fresh usage and effective 4 GiB memory.max/high with zero swap and a five-minute cap. All three usage samples have age zero and 49 percent remaining. Root integration jobs are separate. Prelaunch source-proposal flags are historical drafting records, not current proof status.

This is a finite literal-prefix ledger theorem. It does not prove termination, cover arbitrary internal Parent/native cuts, derive physical word admission without resource assumptions, reconstruct past resources from a later reader, assert writer event uniqueness, supply a common ancestry anchor, or prove actual owner key exclusion. A later selected consumer must use the same Written tuple and its historical Parent execution. The old frozen ledgers, all prior packages, official source, Audit and Haskell files are unchanged by this author component.

I authored this new composition, the existing OuterNativeStores, ActualParentScanNativeStores, and several transitive native positive, scope and corridor foundations. I do not claim independent review of my authored proofs. ResourceParentWriters was authored by arity_meaning; OuterPrefixNativeStores and GeneralParentNativeStores were authored by required_memos. Their exact frozen sources and authority metadata are retained by the approved plan. The independent reviewer authored the local writer foundation and discloses that dependency in the separate independent package.
''')
print('Prepared final selection, ledger and21 source pins; manifest follows verifier creation.')
