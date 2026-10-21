from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
ROOT=Path('/home/tritlo/Code/mcfta')
PREFIX='outer-reference-absent'
def digest(data):return hashlib.sha256(data).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
if not (HERE/'inputs/plan').exists():shutil.copytree('/tmp/mcfta-outer-reference-absent-next-plan',HERE/'inputs/plan')
(HERE/'sourcepins').mkdir(exist_ok=True)
dep='lean/MicroCFTA/SourceCurrentOuterClosedInputs.lean'
blob=(ROOT/dep).read_bytes()
assert digest(blob)=='a4c2f2bfdd3a0be7e5ae88e46e1d816facbee28fa9c6179967a95a8008e490ec'
(HERE/'sourcepins/SourceCurrentOuterClosedInputs.lean').write_bytes(blob)
write('dependency-rootpins.json',{'files':[{'live_path':dep,'snapshot':'sourcepins/SourceCurrentOuterClosedInputs.lean','sha256':digest(blob),'lines':420}]})
source=(HERE/'SourceCurrentOuterReferenceAbsent.lean').read_bytes()
assert digest(source)=='e478e51b56ec1ecf2a613bf7f115688b745c1e01a9b9718c19b643f8f6045263' and len(source.splitlines())==254
proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_bytes().rstrip()
start=source.index(b'theorem no_reference_or_node_absent\n');end=source.index(b' := by',start)
assert source[start:end]==proposal
readback=json.loads((HERE/'full-public-readback.json').read_text());assert readback['source_sha256']==digest(source)
attempts=[]
for stem,kind in [(PREFIX+'-direct-1','strict'),(PREFIX+'-direct-2','strict'),(PREFIX+'-public-1','FULL')]:
 receipt=json.loads((HERE/(stem+'.json')).read_text());raw=(HERE/(stem+'.log')).read_text()
 attempts.append({'name':stem,'kind':kind,'exit_code':receipt['exit_code'],'source_sha256':receipt['sha256'],'receipt':stem+'.json','raw_log':stem+'.log','usage':stem+'.usage.json','limits':stem+'.limits.json','actually_launched':True,'warnings':raw.count('warning:')})
assert [a['exit_code']for a in attempts]==[1,0,0]
write('attempt-ledger.json',{'actual_lean_jobs':3,'failed_jobs':1,'warning_jobs':0,'infrastructure_nonlaunches':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'actual_FULL_jobs':1,'prelaunch_changes_are_zero_jobs':True,'attempts':attempts})
write(PREFIX+'-selection.json',{'finalized':True,'source':'SourceCurrentOuterReferenceAbsent.lean','source_sha256':digest(source),'source_lines':254,'official_path':'lean/MicroCFTA/SourceCurrentOuterReferenceAbsent.lean','selected_strict':PREFIX+'-direct-2','selected_public':PREFIX+'-public-1','groups':[{'name':x['head'],'pairs':1,'kind':'production','full_proof':True}for x in readback['heads']],'actual_axioms_by_head':{x['head']:x['actual_axioms']for x in readback['heads']},'actual_lean_jobs':3,'failed_jobs':1,'warning_jobs':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,'all_eight_settings':True,'actual_type_identity':True,'exact_public_header_proposal':True,'scope':'The actual outer run cannot report unexpectedReference or nodeMemo(absent) under the same genuine initial resource and closed-input packet.','four_line_source_scope_overflow_disclosed':True,'explicit_review_export_ceiling':254,'adequate_fuel_and_completion_unproved':True})
usage=[json.loads((HERE/a['usage']).read_text())for a in attempts]
(HERE/(PREFIX+'-report.md')).write_text(f'''# Reference and absent-node faults at their actual cuts

Final source: SourceCurrentOuterReferenceAbsent.lean,254 lines,SHA {digest(source)}. The sole public no_reference_or_node_absent header is byte-identical to the frozen27-line proposal. It returns the two literal failed-run inequalities for the same requested diagnostic name,handle and final Caller.

The theorem keeps the complete genuine initial packet. It requires Context,Frame,Fits,annotation carrier,phase Inputs,chosen-fuel forecast Room,union normality,native positive Support,causal Mu History,conditional Merge StoredPlain,Merge positive Support,resource writer Origins,NodeStored and InputsClosed. It adds no supplied reached cut,initial idle condition,empty-table condition,closedness of every available heap value or future enclosing return. The shared packet is needed for the reference arm. The absence arm uses only the pure node-table protocol derived from Context.

A private Bool selects exactly unexpectedReference and nodeMemo(absent). It is not an arbitrary diagnostic parameter. One private Cut contains the exact reached reference-body phase with the same failed Caller,or the exact reached node phase and its literal beginNode=(handle,absent,after) tuple. Six private At predicates universally quantify the ten lower numeric parameters. One strong-fuel induction follows the literal six-phase worker. It reuses the actual Outcome.bind inverse and ExecutionAncestry.Step constructors from the existing ParentFailure proof pattern. Only completed earlier siblings contribute their literal done equations. Failed continuations preserve the same Caller. No completed future suffix or stronger activation graph is assumed. Edge calls can emit only edge memo or Parent diagnostics and cannot emit either selected fault.

The public reference arm calls OuterClosedInputs.reached once on the exact returned reference-body cut. InputsClosed there reduces to[name]=[],which is impossible. It does not inspect references bound inside an opaque Mu. The absence arm derives initial NodeValid from Context.sound.valid.nodes with the existing FlatMemoThunk.Valid.keyMap. Reached.valid transports that pure protocol to the exact beginNode cut. A missing table key publishes a suspended cell,so demand evaluates it. A present key has a present cell by Valid.linked. No status of that present cell is absent. This arm needs no NodeIdle,EdgeIdle,current semantic heap,canonical request equality or closure law.

The source draft recipe initially contained254 total Lean lines. This exceeded the original250-line stop by4 lines. The first writer script reported the overflow and withheld the .lean export,but the recipe already constituted a source draft. The scope-exception report explicitly records that real overflow. Root and guard read the complete recipe and rendered source. Root then authorized254 lines for review-only export. The unchanged original254 source SHA48c8a6a0 and unchanged generator SHA827d6ee2 are retained. Seven reviewed same-line selector corrections produced254/67b68404 before the first compiler check. Five immediate nonmatching faults split the selector;both public specializations bind their existing name and handle explicitly. No blank-line compression or additional framework was used to satisfy the exception. The original frozen plan and its historical pending dependency status remain unchanged under inputs/plan. A separate dependency cue records the official420-line OuterClosedInputs source,a4c2f2bf,root strict success and Audit3612jobs/75069dependencies.

There are three actual author Lean commands. Strict1 genuinely failed with one application-type error and no warning. The rows specialization supplied16 placeholders for17 parameters,so its failed equation was supplied where the final Caller argument belonged. The full558-byte raw log,source254/67b68404,receipt,usage and effective limits are retained. Root and guard reviewed the complete raw log and one-extra-underscore patch before root authorized its application and strict2. The public header and mathematical route did not change. Strict2 passed with a literally empty raw log. The sole FULLpublic1 passed. No other proof command was run.

The hardened complete readback verified all eight printer settings,whole check/print TYPE identity,a unique actual lambda-body delimiter,no omissions and no private identifiers in the public TYPE. Its actual axiom set is {readback['heads'][0]['actual_axioms']}. The complete public log has {readback['log_bytes']}bytes,SHA {readback['log_sha256']}. The printer SHA is {readback['printer_sha256']}. The normalized TYPE has {readback['heads'][0]['normalized_type_characters']}characters and the proof body has {readback['heads'][0]['body_characters']}characters. The metadata reader passed on its first run.

Actual inventory:3author Lean jobs,1failed strict,0warning jobs,0infrastructure nonlaunches,0canonical jobs,0runtime examples,0constructed pairs and1production public pair. Fresh weekly remaining percentages are {[x['remaining_percent']for x in usage]},with ages {[x['age_seconds']for x in usage]}seconds. Every worker checked MemoryMax=MemoryHigh=4294967296bytes and memory.swap.max=0. Each wrapper imposed five minutes. Every attempt retains its immutable source input,complete raw log,receipt,usage and effective-limit record. Root checks and reviewer checks are separate from this author inventory.

This theorem excludes only unexpectedReference and nodeMemo(absent). It does not exclude every remaining diagnostic or prove the existence of a first sufficient outer fuel,a finite-width capacity envelope,finite renewals or unrestricted termination. Existing chosen-fuel resource assumptions remain explicit. The result does not turn done_stable into an existence theorem.

The author wrote ResourceParentClosed and several resource/native adapters used by the genuine packet. This package does not claim independent review of those authored foundations. The new cut inverse follows the existing ParentFailure pattern;it does not change that module. Guard independently reviewed the new composition,the complete254-line source,the scope exception,the selector patch,the full failed log and the one-underscore repair. Root owns official installation,Audit and repository checks. This component changed no official source,Audit file,Git state,shared board or earlier frozen package.
''')
excluded={PREFIX+'-manifest.json',PREFIX+'-verification.json',PREFIX+'-live-verification.json'}
files=[]
for q in sorted(HERE.rglob('*')):
 relative=q.relative_to(HERE).as_posix()
 if q.is_file() and relative not in excluded:
  data=q.read_bytes();files.append({'path':relative,'bytes':len(data),'sha256':digest(data)})
write(PREFIX+'-manifest.json',{'finalized':True,'source_sha256':digest(source),'actual_lean_jobs':3,'failed_jobs':1,'files':files})
print(json.dumps({'manifest_sha256':digest((HERE/(PREFIX+'-manifest.json')).read_bytes()),'selection_sha256':digest((HERE/(PREFIX+'-selection.json')).read_bytes()),'report_sha256':digest((HERE/(PREFIX+'-report.md')).read_bytes()),'local_pins':len(files)},indent=2))
