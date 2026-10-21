from pathlib import Path
import hashlib
import json
import shutil

HERE=Path(__file__).resolve().parent
PREFIX='older-owner-busy'
def sha(data):
    return hashlib.sha256(data).hexdigest()
def write(name,value):
    (HERE/name).write_text(json.dumps(value,indent=2)+'\n')

shutil.copytree('/tmp/mcfta-older-owner-busy-next-plan',HERE/'inputs/plan')
source=(HERE/'SourceCurrentOlderOwnerBusy.lean').read_bytes()
text=source.decode()
proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
actual=text[text.index('theorem no_node_busy'):text.index('\n := by\n',text.index('theorem no_node_busy'))]
expected=proposal[proposal.index('theorem no_node_busy'):proposal.index('\nend MicroCFTA')]
assert actual==expected and len(text.splitlines())==69
shutil.copyfile(HERE/'source-proposal.json',HERE/'source-proposal-prelaunch.json')
comparison=json.loads((HERE/'source-proposal.json').read_text())
comparison.update(source_sha256=sha(source),selected_source=True,
    status='Checked busy-node exclusion; finite renewal and completion remain outside this component.')
write('source-proposal.json',comparison)
readback=json.loads((HERE/'full-public-readback.json').read_text())
assert readback['source_sha256']==sha(source)
attempts=[]
for stem,kind in [(PREFIX+'-direct-1','strict'),(PREFIX+'-public-1','FULL')]:
    receipt=json.loads((HERE/(stem+'.json')).read_text())
    assert receipt['exit_code']==0
    attempts.append({'name':stem,'kind':kind,'exit_code':0,'source_sha256':receipt['sha256'],
        'receipt':stem+'.json','raw_log':stem+'.log','usage':stem+'.usage.json',
        'limits':stem+'.limits.json','actually_launched':True})
write('attempt-ledger.json',{'actual_lean_jobs':2,'failed_jobs':0,'warning_jobs':0,
    'infrastructure_nonlaunches':0,'canonical_jobs':0,'runtime_jobs':0,'constructed_pairs':0,
    'prelaunch_source_changes':0,'attempts':attempts})
write(PREFIX+'-selection.json',{'finalized':True,'source':'SourceCurrentOlderOwnerBusy.lean',
    'source_sha256':sha(source),'source_lines':69,
    'official_path':'lean/MicroCFTA/SourceCurrentOlderOwnerBusy.lean',
    'selected_strict':PREFIX+'-direct-1','selected_public':PREFIX+'-public-1',
    'groups':[{'name':head['head'],'pairs':1,'kind':'production','full_proof':True} for head in readback['heads']],
    'actual_axioms_by_head':{head['head']:head['actual_axioms'] for head in readback['heads']},
    'actual_lean_jobs':2,'failed_jobs':0,'warning_jobs':0,'canonical_jobs':0,'runtime_jobs':0,
    'constructed_pairs':0,'all_eight_settings':True,'actual_type_identity':True,
    'exact_public_header_proposal':True,'initial_node_idle_explicit':True,
    'scope':'Excludes outer nodeMemo busy for every enclosing activation; does not prove finite renewal or completion.'})
usage=[json.loads((HERE/attempt['usage']).read_text()) for attempt in attempts]
(HERE/(PREFIX+'-report.md')).write_text(f'''# Busy-node exclusion for every enclosing activation

Final source: SourceCurrentOlderOwnerBusy.lean, 69 lines, SHA {sha(source)}. Its sole public no_node_busy statement is byte-identical to the frozen proposed declaration. No prelaunch or postlaunch source correction was needed.

The theorem excludes a literal outer nodeMemo(handle,busy) failure from an arbitrary initial Phase. It retains genuine initial Context, Frame, resource bounds, annotations, Inputs, normality, native Support, causal Mu History, conditional Merge storage, positive Merge Support and resource writer Origins. Its additional initialNodeIdle premise says that no node cell is evaluating at entry. The standard State.initial has empty node and edge tables and satisfies this boundary. Warm suspended or returned cells are permitted when the genuine packet holds. Arbitrary evaluating initial cells are excluded because they need not come from this run's activation history.

One existing OuterInitialBusy.busy call derives the exact reached fault request and the evaluating cell containing that SAME full request. That checked producer already derives canonical inherited and constructor equality at the current fault heap. The new source does not copy or export an equality helper. A one-line public keyMap projection supplies entry NodeValid. Reached.owners uses the same reached cut, initial idle and exact evaluating cell to recover its actual earlier activation and unfinished body prefix. The source appends that literal activation step and calls body_rank_lt once. Both rank endpoints are the same full request. Cases on the lexicographic proof contradict Nat.lt_irrefl. There is no induction, new rank, selected owner oracle, future completion premise or additional framework.

Root and guard read all 69 source lines, exact public header and dependency contracts before strict1. Selected strict1 passed with a literally empty raw log. The sole FULLpublic1 passed. The hardened reader verified all eight printer settings, exact complete check/print TYPE identity, the unique actual lambda proof delimiter, no omissions and no private public TYPE identifiers. The measured actual axiom set is {readback['heads'][0]['actual_axioms']}.

The complete public log has {readback['log_bytes']} bytes and SHA {readback['log_sha256']}. The printer SHA is {readback['printer_sha256']}. Its normalized public TYPE has {readback['heads'][0]['normalized_type_characters']} characters; its complete proof body has {readback['heads'][0]['body_characters']} characters. The reader passed on its first metadata run. No additional proof check was used to produce that metadata.

There are two actual author Lean commands and zero failures, warnings, infrastructure nonlaunches, canonical jobs, runtime tests or constructed examples. Each command has an immutable input, raw log, receipt, fresh usage record and effective-limit record. Weekly remaining percentages are {[item['remaining_percent'] for item in usage]}; ages are {[item['age_seconds'] for item in usage]} seconds. Each worker verified MemoryMax=MemoryHigh=4294967296 bytes and memory.swap.max=0. Each capped wrapper imposed five minutes. The peak records remain in older-owner-busy-peaks.txt.

Every enclosing active node ancestor is covered by the existing owners theorem. This is not a proof that every fault constructor is impossible. The checked EdgeIdle APIs separately exclude outer edge-busy faults from edge-idle entry states. This component does not prove finite fresh renewal, fuel-independent completion, successful termination, or absence of exhausted, absent, reference, binder or Parent faults. It adds no new implementation correspondence claim.

The author wrote the count, one-hop rank, local resource writer, selected certificates and related positive-chronology foundations. This component does not claim independent review of those authored foundations. The body-rank dependency was authored separately. Guard independently reviewed the new composition and complete source. Root owns official installation, independent strict checking and Audit; those commands are excluded from this component's two author commands. The frozen source-only plan in inputs/plan keeps its historical dependency readiness cue unchanged.
''')
excluded={PREFIX+'-manifest.json',PREFIX+'-verification.json',PREFIX+'-live-verification.json'}
files=[]
for path in sorted(HERE.rglob('*')):
    if path.is_file() and path.name not in excluded:
        data=path.read_bytes()
        files.append({'path':str(path.relative_to(HERE)),'bytes':len(data),'sha256':sha(data)})
write(PREFIX+'-manifest.json',{'finalized':True,'source_sha256':sha(source),'actual_lean_jobs':2,
    'failed_jobs':0,'files':files})
print(json.dumps({'manifest_sha256':sha((HERE/(PREFIX+'-manifest.json')).read_bytes()),
    'selection_sha256':sha((HERE/(PREFIX+'-selection.json')).read_bytes()),'local_pins':len(files)}))
