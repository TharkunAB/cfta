from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
PREFIX='outer-done-or-exhausted'
def digest(data):return hashlib.sha256(data).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
if not(HERE/'inputs/plan').exists():shutil.copytree('/tmp/mcfta-outer-done-or-exhausted-next-plan',HERE/'inputs/plan')
(HERE/'sourcepins').mkdir(exist_ok=True)
rel='lean/MicroCFTA/SourceCurrentOuterLocalFaults.lean';data=(ROOT/rel).read_bytes()
assert digest(data)=='aeb5829ae30afb8ff8cbeceb4d159c1414141e2e39298cbdf55f69308aad9c4a'
(HERE/'sourcepins/SourceCurrentOuterLocalFaults.lean').write_bytes(data)
write('dependency-rootpins.json',{'files':[{'live_path':rel,'snapshot':'sourcepins/SourceCurrentOuterLocalFaults.lean','sha256':digest(data),'lines':216}]})
source=(HERE/'SourceCurrentOuterDoneOrExhausted.lean').read_bytes();assert len(source.splitlines())==83
assert source==(HERE/'done-or-exhausted-source-only.lean.txt').read_bytes()
assert digest(source)=='b6485bba37a65fd0358d00517605198c7ad74d53d1341d13ab0c6093f10cc3ce'
proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_bytes().rstrip()
start=source.index(b'theorem done_or_exhausted\n');end=source.index(b' := by',start);assert source[start:end]==proposal
readback=json.loads((HERE/'full-public-readback.json').read_text());assert readback['source_sha256']==digest(source)
attempts=[]
for stem,kind in [(PREFIX+'-direct-1','strict'),(PREFIX+'-public-1','FULL')]:
 r=json.loads((HERE/(stem+'.json')).read_text());assert r['exit_code']==0
 attempts.append({'name':stem,'kind':kind,'exit_code':0,'source_sha256':r['sha256'],'receipt':stem+'.json','raw_log':stem+'.log','usage':stem+'.usage.json','limits':stem+'.limits.json','actually_launched':True})
write('attempt-ledger.json',{'actual_lean_jobs':2,'failed_jobs':0,'warning_jobs':0,'infrastructure_nonlaunches':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'actual_FULL_jobs':1,'attempts':attempts})
write(PREFIX+'-selection.json',{'finalized':True,'source':'SourceCurrentOuterDoneOrExhausted.lean','source_sha256':digest(source),'source_lines':83,'official_path':'lean/MicroCFTA/SourceCurrentOuterDoneOrExhausted.lean','selected_strict':PREFIX+'-direct-1','selected_public':PREFIX+'-public-1','groups':[{'name':x['head'],'pairs':1,'kind':'production','full_proof':True}for x in readback['heads']],'actual_axioms_by_head':{x['head']:x['actual_axioms']for x in readback['heads']},'actual_lean_jobs':2,'failed_jobs':0,'warning_jobs':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'all_eight_settings':True,'actual_type_identity':True,'exact_public_header_proposal':True,'hard_stop_total_source_lines':150,'scope':'The same actual chosen-fuel outer run is done or reports outer-fuel exhaustion under all explicit initial resource and fuel assumptions.','adequate_outer_fuel_and_joint_Room_unproved':True,'unrestricted_completion_unproved':True})
usage=[json.loads((HERE/a['usage']).read_text())for a in attempts]
(HERE/(PREFIX+'-report.md')).write_text(f'''# Actual chosen-fuel outer run: done or exhausted

Final source: SourceCurrentOuterDoneOrExhausted.lean,83lines,SHA {digest(source)}. Its sole public done_or_exhausted header is byte-identical to the frozen34-line proposal. The complete approved83-line source passed without a prelaunch correction or postlaunch source change. It is below the explicit150TOTAL source ceiling.

The theorem keeps the genuine initial Context,Frame,Fits,annotation carrier,phase Inputs,chosen-phase forecast Room,union normality,native positive Support,causal Mu History,conditional Merge StoredPlain,Merge positive Support and resource writer Origins. It also keeps NodeStored,InputsClosed,initial node idleness,initial EdgeIdle and all nine explicit phaseNeed inequalities. These are hypotheses,not conclusions of this theorem. The initial tables need not be empty. No desired success,supplied reached cut,future return,adequate outer fuel or capacity oracle is added.

The conclusion gives either an actual run=.done()after equation or an actual run=.failed(.exhausted limit)after equation. Both retain the same chosen Phase,the same nine lower bounds and conjunction budget,and the literal resulting Caller. ActiveAncestry.run erases only successful phase output,so this theorem does not separately return that erased node,row or child value. The exhausted witness is an actual Limit.nodeBody,Limit.rows or Limit.walk.

The proof makes one actual Outcome case split. Its done branch cases the Unit value and retains the literal Caller. Its failed branch calls checked LocalFaults.failed_cases exactly once on that same failed equation and initial packet. It keeps exhaustion. It removes node busy with OlderOwnerBusy.no_node_busy and the genuine initialNodeIdle packet. It removes node absent and unexpectedReference with the corresponding ReferenceAbsent projections. Literal.depth and0fill only their unused paired arguments. It removes every edgeMemo payload with InitialEdgeMemoFailure.no_edge_memo_failure and initialEdgeIdle. It removes every Parent observation with InitialParentFailure.no_parent_failure and all nine original phaseNeed bounds. The restricted nodeMemo alternatives come from actual LocalFaults provenance,not from the more general diagnostic datatype. Every exclusion consumes the same failed Caller equation. No inverse,induction,datatype,private helper or public fault predicate is added.

The frozen source-only plan remains unchanged under inputs/plan. It preserves the historical14:04 unchecked dependency cue,the original plan and its exact one-line status correction,the separate150-line stop and the later status cue. A separate proof-package readiness record documents official LocalFaults216/aeb5829a compilation and root Audit3614jobs/75095dependencies. The actual checked LocalFaults source is pinned separately. This does not retrofit a checked status into the frozen historical plan.

Root and guard read the complete source,exact public header and dependency readiness before root authorized the first check on a fresh preserved checkpoint. Strict1 passed with a literally empty raw log. The sole FULLpublic1 passed. The hardened reader passed on its first run. It verified all eight printer settings,complete check/print TYPE identity,a unique actual lambda-body delimiter,no omissions,no private public TYPE names and actual axioms {readback['heads'][0]['actual_axioms']}. The full log has {readback['log_bytes']}bytes,SHA {readback['log_sha256']}. The printer SHA is {readback['printer_sha256']}. The normalized TYPE has {readback['heads'][0]['normalized_type_characters']}characters and its proof body has {readback['heads'][0]['body_characters']}characters.

There are2actual author Lean commands,0failures,0warnings,0infrastructure nonlaunches,0canonical jobs,0runtime examples,0constructed pairs and1production public pair. Both commands retain their immutable input,complete raw log,receipt,fresh usage and effective-limit record. Weekly remaining percentages were {[x['remaining_percent']for x in usage]},with ages {[x['age_seconds']for x in usage]}seconds. Each worker checked MemoryMax=MemoryHigh=4294967296bytes and memory.swap.max=0. Every wrapper imposed five minutes. Root's independent strict and Audit are separate commands and are not included in this author inventory.

The first jointly adequate OUTER fuel and genuine initial Room for that SAME forecast remain unproved. phaseNeed bounds the lower workers at a chosen phase. Room at one forecast need not hold at a larger fuel or fixed width. Existing graph completion assumes a finite actual graph,and success stability assumes an actual success. This theorem does not construct either the first success or a noncircular resource envelope. A rank-driven graph/envelope or proved width/state/fuel transport remains a separate obligation. No unrestricted completion or implementation termination is claimed.

The author wrote ReferenceAbsent,ResourceParentClosed and related resource/native adapters used by the initial packet. This package does not claim independent certification of those authored foundations. Guard independently reviewed this new composition and its exact source. Root owns official installation,Audit and repository checks. No official source,Audit file,Git state,shared board or earlier frozen package was changed by this component.
''')
excluded={PREFIX+'-manifest.json',PREFIX+'-verification.json',PREFIX+'-live-verification.json'}
files=[]
for q in sorted(HERE.rglob('*')):
 rel=q.relative_to(HERE).as_posix()
 if q.is_file() and rel not in excluded:
  data=q.read_bytes();files.append({'path':rel,'bytes':len(data),'sha256':digest(data)})
write(PREFIX+'-manifest.json',{'finalized':True,'source_sha256':digest(source),'actual_lean_jobs':2,'failed_jobs':0,'files':files})
print(json.dumps({'manifest_sha256':digest((HERE/(PREFIX+'-manifest.json')).read_bytes()),'selection_sha256':digest((HERE/(PREFIX+'-selection.json')).read_bytes()),'report_sha256':digest((HERE/(PREFIX+'-report.md')).read_bytes()),'local_pins':len(files)},indent=2))
