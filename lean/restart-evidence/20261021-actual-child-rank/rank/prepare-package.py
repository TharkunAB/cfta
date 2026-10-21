from pathlib import Path
import hashlib
import json
import re
import shutil

HERE=Path(__file__).resolve().parent
PREFIX='actual-child-rank'
def sha(data):
    return hashlib.sha256(data).hexdigest()
def write(name,value):
    (HERE/name).write_text(json.dumps(value,indent=2)+'\n')

shutil.copytree('/tmp/mcfta-actual-child-rank-next-plan',HERE/'inputs/plan')
source=(HERE/'SourceCurrentActualChildRank.lean').read_bytes()
text=source.decode()
proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
expected=proposal[proposal.index('theorem dispatch'):proposal.index('\nend MicroCFTA')]
actual=text[text.index('theorem dispatch'):text.index('\n := by\n',text.index('theorem dispatch'))]
assert actual==expected and len(text.splitlines())<250
shutil.copyfile(HERE/'source-proposal.json',HERE/'source-proposal-prechecks.json')
comparison=json.loads((HERE/'source-proposal.json').read_text())
comparison.update(source_sha256=sha(source),source_lines=len(text.splitlines()),
    selected_source=True,header_exact=True,implementation_status='Checked one-hop rank; whole-lineage rank and completion remain unproved.')
write('source-proposal.json',comparison)
readback=json.loads((HERE/'full-public-readback.json').read_text())
assert readback['source_sha256']==sha(source)
receipts=sorted([path for path in HERE.glob(PREFIX+'-direct-*.json')
    if re.fullmatch(PREFIX+r'-direct-\d+\.json',path.name)],
    key=lambda path:int(path.stem.rsplit('-',1)[1]))
ledger=[]
for path in receipts+[HERE/(PREFIX+'-public-1.json')]:
    receipt=json.loads(path.read_text())
    stem=path.stem
    raw=(HERE/(stem+'.log')).read_text()
    ledger.append({'name':stem,'kind':'FULL' if '-public-' in stem else 'strict',
        'exit_code':receipt['exit_code'],'source_sha256':receipt['sha256'],
        'receipt':path.name,'raw_log':stem+'.log','usage':stem+'.usage.json',
        'limits':stem+'.limits.json','actually_launched':True,
        'warning_bearing':bool(re.search(r'\bwarning(?:\([^)]*\))?:',raw))})
assert [entry['exit_code'] for entry in ledger]==[1,1,1,1,0,0]
assert [entry['warning_bearing'] for entry in ledger]==[False,False,False,True,False,False]
write('attempt-ledger.json',{'actual_lean_jobs':len(ledger),
    'failed_jobs':sum(entry['exit_code']!=0 for entry in ledger),
    'warning_jobs':sum(entry['warning_bearing'] for entry in ledger),
    'infrastructure_nonlaunches':0,'canonical_jobs':0,'runtime_jobs':0,
    'constructed_pairs':0,'attempts':ledger})
write(PREFIX+'-selection.json',{'finalized':True,'source':'SourceCurrentActualChildRank.lean',
    'source_sha256':sha(source),'source_lines':len(text.splitlines()),
    'official_path':'lean/MicroCFTA/SourceCurrentActualChildRank.lean',
    'selected_strict':receipts[-1].stem,'selected_public':PREFIX+'-public-1',
    'groups':[{'name':head['head'],'pairs':1,'kind':'production','full_proof':True} for head in readback['heads']],
    'actual_axioms_by_head':{head['head']:head['actual_axioms'] for head in readback['heads']},
    'actual_lean_jobs':len(ledger),'failed_jobs':4,'warning_jobs':1,
    'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,
    'all_eight_settings':True,'actual_type_identity':True,
    'no_active_owner_or_caller_back_premise':True,'exact_public_header_proposal':True,
    'scope':'actual one-hop strict lex count/mass rank; older lineage/completion remain unproved'})
usage=[json.loads((HERE/entry['usage']).read_text()) for entry in ledger]
(HERE/(PREFIX+'-report.md')).write_text(f'''# Actual one-hop child rank

Final source: SourceCurrentActualChildRank.lean,{len(text.splitlines())}lines, SHA{sha(source)}. The sole public dispatch returns the literal selected child Reached and a strict lexicographic decrease in inherited positive-class count and complete structural mass. Its statement is byte-identical to the frozen proposed declaration.

The theorem uses genuine initial Context, Frame, resource bounds, annotations, input availability, normality, native Support, causal Mu history, conditional Merge storage, positive Merge support and resource writer Origins. It retains the actual row prefix, one completed Parent return, its actual current inherited prefix, the completed earlier child walk, exact selected child lookup and membership of the same original row in a literal ordinary container. It needs no evaluating active owner, copied-owner equality, key collision, supplied backwards relation, future child completion or rank oracle.

One local resource edge_call obtains the same historical Parent Written. The actual current accessor and combination derive coherent fixed combined records and inherited coverage. The checked all-child Back producer is called once on that Written. The checked quotient child_count is called once on its exact selected child. The actual late walk return transfers combined readiness. descend_correct identifies the literal inherited payload at that actual late state, including cached winners.

A nonplain source row gives strict count descent. For a plain row, the actual plain test implies empty source equalities in one direction. The returned conditional Shape gives an original proper child or literal Empty. This yields strict structural mass when the count bound is only weak. No structural mass bound is used on a changed nonplain child. Mu, references and union children require no extra constructor assumption or child execution.

The complete first draft reached the mandatory250-line stop. No compiler ran there. Root read it and authorized removal of only the unused private prefix growth output and proof. The caller already uses the actual walk Post growth. The original250 source and exact trim remain. The trimmed248 source passed both full source reviews before strict1. No public statement changed.

Four real strict checks failed. Strict1 used the nonexistent Bool.and_eq_true.mp name. Its one-line repair uses Bool.and_eq_true_iff.mp. Strict2 had one untyped shape_mass call; four diagnostics identified its unconstrained literal entry/depth/free arguments. Its two-line repair supplies those same container fields. Strict3 needed the some/getD wrappers reduced before its syntactic count equality rewrite. Strict4 showed that simultaneous simp unfolded the payload projection before the exact payload equality could apply; it also reported one unused-simp-argument warning. The final one-line repair sequences the exact payload rewrite before wrapper reduction. Root and guard reviewed each complete raw diagnostic and exact patch before the next launch. All immutable inputs, raw logs, patches and receipts remain.

Root reviewed the larger strict2/3/4 contexts through lossless line deduplication with exact reconstruction hashes. Those review JSON files remain as zero-job metadata. A diagnostic count is not a command count. The source-only prelaunch trim is not a failed check. No failure was classified as infrastructure or as a mathematical counterexample.

Selected strict5 passed with a literally empty raw log. The sole FULLpublic1 passed. The hardened reader verified the complete check/print TYPE pair, unique actual lambda body delimiter, all eight printer settings, no omissions and no private public TYPE identifiers. The measured actual axiom set is {readback['heads'][0]['actual_axioms']}. The complete public output is{readback['log_bytes']}bytes, SHA{readback['log_sha256']}. Its printer SHA is{readback['printer_sha256']}.

There are six actual author Lean commands: four failed stricts, one clean selected strict and one clean FULL. Only strict4 bears a warning. There are no canonical jobs, runtime tests, constructed examples or infrastructure nonlaunches. Each launch has a separate immutable source, raw log, receipt, fresh usage record and effective cgroup-limit record. Weekly remaining percentages in command order are{[item['remaining_percent'] for item in usage]}; ages are{[item['age_seconds'] for item in usage]}seconds. Every worker verified MemoryMax=MemoryHigh=4294967296bytes and memory.swap.max=0. Every wrapper imposed five minutes. Peak records remain unchanged in actual-child-rank-peaks.txt.

This theorem proves an actual one-hop rank bound in the checked caller graph. It does not compose that bound across arbitrary older active ancestors, prove the separate body_rank_lt target, remove genuine initial laws, prove whole-call termination, or establish new implementation correspondence. No source family or runtime example was added.

The author wrote the local resource writer, selected certificates, earlier immediate inherited consumer, quotient count and several positive-chronology foundations. This component does not claim an independent review of those authored foundations. Guard independently reviewed this new composition and every repair. Root owns official installation, independent strict checking and Audit; its commands are not part of the six author commands. The frozen source-only plan remains unchanged in inputs/plan, including its historical pending status and separate later checked dependency cue.
''')
excluded={PREFIX+'-manifest.json',PREFIX+'-verification.json',PREFIX+'-live-verification.json'}
files=[]
for path in sorted(HERE.rglob('*')):
    if path.is_file() and path.name not in excluded:
        data=path.read_bytes()
        files.append({'path':str(path.relative_to(HERE)),'bytes':len(data),'sha256':sha(data)})
write(PREFIX+'-manifest.json',{'finalized':True,'source_sha256':sha(source),
    'actual_lean_jobs':len(ledger),'failed_jobs':4,'files':files})
print(json.dumps({'manifest_sha256':sha((HERE/(PREFIX+'-manifest.json')).read_bytes()),
    'selection_sha256':sha((HERE/(PREFIX+'-selection.json')).read_bytes()),'local_pins':len(files)}))
