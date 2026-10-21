#!/usr/bin/env python3
"""Verify frozen outer writer proof evidence without running Lean."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

PREFIX='outer-resource-writers-'
HEAD='MicroCFTA.SourceCurrentOuterResourceWriters.reached'
SOURCE_SHA='50ae9ee05230de797cfe71b68c0fb016b4352f763c99161b98708fb9d20ceab5'

def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(p: Path) -> dict:
    return json.loads(p.read_text())

def relative(value: str) -> Path:
    p=Path(value);assert not p.is_absolute() and '..' not in p.parts
    return p

def check(p: Path,pin: dict) -> None:
    assert p.is_file() and p.stat().st_size==pin['bytes'] and sha(p)==pin['sha256'],str(p)

def instant(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z','+00:00'))

def main() -> None:
    parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True);parser.add_argument('--live',action='store_true')
    args=parser.parse_args();here=Path(__file__).resolve().parent
    manifest=read(here/(PREFIX+'manifest.json'));assert manifest['finalized']
    for pin in manifest['files']:check(here/relative(pin['path']),pin)
    pins=read(here/(PREFIX+'source-pins.json'))['files'];assert pins==manifest['sources']
    for pin in pins:
        snapshot=here/relative(pin['snapshot']);check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            assert 1<=span['start']<=span['end']<=len(lines)
            assert hashlib.sha256(b''.join(lines[span['start']-1:span['end']])).hexdigest()==span['sha256']
        if args.live:check(args.root/relative(pin['path']),pin)
    selected=read(here/(PREFIX+'selection.json'));assert selected['finalized']
    assert selected['public_heads']==[HEAD] and selected['new_public_pairs']==1
    assert selected['canonical_jobs']==selected['constructed_pairs']==selected['infrastructure_attempts']==selected['prelaunch_proof_commands']==0
    assert not selected['official_edits_by_author'] and selected['public_headers_match_frozen_proposal']
    source=here/relative(selected['source']);text=source.read_text()
    assert sha(source)==SOURCE_SHA==selected['source_sha256'] and len(text.splitlines())==selected['source_lines']==465
    assert re.findall(r'^theorem (\w+)',text,re.M)==['reached']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b',text)
    proposed=(here/'inputs/plan/proposed-signature.lean.txt').read_text()
    actual_header=text.split('theorem reached',1)[1].split(' := by',1)[0].strip()
    proposed_header=proposed.split('theorem reached',1)[1].split('\nend ',1)[0].strip()
    assert actual_header==proposed_header
    assert actual_header.endswith('SourceCurrentResourceParentWriters.Origins formulas solver (caller last)')
    assert '(origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))' in actual_header
    assert text.count('SourceCurrentResourceParentWriters.edge_call formulas solver')==1
    assert text.count('SourceCurrentOuterPrefixNativeStores.reached formulas solver')==1
    assert text.count('change Origins formulas solver middle')==2
    for kind in ['NodeCallAt','NodeBodyAt','RowsAt','DescendantsAt','ChildrenAt','WalkAt']:
        assert 'private def '+kind+' ' in text
    assert 'History.retain' not in text and 'NoNewMu' not in text and 'FlatMemoThunk.finish_spec' not in text
    original=(here/'outer-resource-writers-prelaunch-461.lean').read_text()
    failed=(here/(PREFIX+'direct-1.source.lean')).read_text()
    assert hashlib.sha256(original.encode()).hexdigest()==selected['initial_prelaunch_sha256']
    assert hashlib.sha256(failed.encode()).hexdigest()==selected['actual_failed_source_sha256']
    assert failed==original.replace('  have reserved := reservation formulas solver initial fits known inherited resident uniform',
        '  have reserved := reservation formulas solver (request := request) initial fits known inherited resident uniform')
    expected=failed.replace(
        '            SourceCurrentOuterInitialActual.node_call formulas solver fuel seed descentPost.context descentFrame descentFits known',
        '            SourceCurrentOuterInitialActual.node_call formulas solver fuel\n              (request := ⟨(descend before combined index).1,value⟩) (before := (descend before combined index).2) seed descentPost.context descentFrame descentFits known').replace(
        '          have headStores := SourceCurrentOuterNativeStores.node_call formulas solver fuel seed',
        '          have headStores := SourceCurrentOuterNativeStores.node_call formulas solver fuel\n            (request := ⟨(descend before combined index).1,value⟩) (before := (descend before combined index).2) seed').replace(
        '              exact child seed prefixPost.context prefixFrame prefixFits known prefixReceipt.combinedReady',
        '              change Origins formulas solver middle\n              exact child seed prefixPost.context prefixFrame prefixFits known prefixReceipt.combinedReady').replace(
        '              exact rowCalls fuel (Nat.lt_succ_self _) seed initial frame fits known inherited edges rowsRoom first stores origins',
        '              change Origins formulas solver middle\n              exact rowCalls fuel (Nat.lt_succ_self _) seed initial frame fits known inherited edges rowsRoom first stores origins').replace(
        '        head_edge formulas solver seed initial frame fits known inputs.1 (inputs.2 _ List.mem_cons_self)',
        '        head_edge formulas solver (request := ⟨inherited,original⟩) seed initial frame fits known inputs.1 (inputs.2 _ List.mem_cons_self)')
    assert expected==text
    ledger=read(here/(PREFIX+'attempt-ledger.json'))['attempts']
    assert len(ledger)==len({item['name'] for item in ledger})==selected['lean_jobs']==3
    assert {item['name']:item['exit_code'] for item in ledger}=={PREFIX+'direct-1':1,PREFIX+'direct-2':0,PREFIX+'public-1':0}
    receipt_names={p.stem for p in here.glob(PREFIX+'*.json') if re.fullmatch(PREFIX+r'(?:direct|public)-\d+',p.stem)}
    assert receipt_names=={item['name'] for item in ledger}
    failed_count=warning_count=0
    for item in ledger:
        stem=item['name'];receipt=read(here/(stem+'.json'));log=here/(stem+'.log')
        assert item['kind']=='lean' and item['lean_launched'] and receipt['exit_code']==item['exit_code']
        assert sha(here/(stem+'.json'))==item['receipt_sha256'] and sha(log)==item['log_sha256']
        assert sha(here/relative(receipt['source']))==receipt['sha256']
        assert receipt['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert receipt['command'][1]=='-Dlinter.all=true' and receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
        assert read(here/relative(receipt['limits']))=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=read(here/(stem+'.usage.json'));assert 0<=usage['age_seconds']<120 and usage['remaining_percent']>1
        start,end=instant(receipt['started_at']),instant(receipt['observed_at'])
        assert 0<=(start-instant(usage['observed_at'])).total_seconds()<120 and 0<=(end-start).total_seconds()<300
        warnings=len(re.findall(r'\bwarning(?:\([^)]*\))?:',log.read_text()))
        assert warnings==item['warning_diagnostics']
        warning_count+=warnings>0;failed_count+=receipt['exit_code']!=0
    assert failed_count==selected['failed_checks']==1 and warning_count==selected['warning_checks']==0
    strict=selected['selected_strict'];public=selected['selected_public']
    assert read(here/(strict+'.json'))['exit_code']==read(here/(public+'.json'))['exit_code']==0
    assert (here/(strict+'.log')).read_bytes()==b'' and (here/(strict+'.source.lean')).read_bytes()==source.read_bytes()
    printer=(here/(public+'.source.lean')).read_text()
    assert printer==(here/(PREFIX+'public.lean')).read_text() and printer.startswith(text+'\n')
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert printer.count('set_option '+option)==1
    for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+HEAD)==1
    log_path=here/(public+'.log');assert log_path.stat().st_size==selected['public_log_bytes']==451700
    assert sha(log_path)==selected['public_log_sha256']
    log=log_path.read_text();assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    checked,printed=log.split('@'+HEAD+' :',1)[1].split('\ntheorem '+HEAD+' :',1)
    declared,proof=printed.split(' :=',1);assert ''.join(checked.split())==''.join(declared.split())
    assert '_private' not in checked+declared and 'NodeCallAt' not in checked+declared and 'Stores' not in checked+declared
    ax=re.search(re.escape("'"+HEAD+"' depends on axioms:")+r'\s*\[([^\]]*)\]',proof);assert ax and len(proof[:ax.start()])>1000
    names=sorted(x.strip() for x in re.sub(r'\.\{[^}]*\}','',ax.group(1)).split(','))
    assert names==selected['axioms_by_head'][HEAD]==['Classical.choice','Quot.sound','propext']
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),'lean_jobs':3,'failed_checks':1,'warning_checks':0,'infrastructure_attempts':0,'canonical_jobs':0,'public_heads':[HEAD],'constructed_pairs':0,'public_type_identity':True,'axioms_by_head':selected['axioms_by_head'],'manifest_sha256':sha(here/(PREFIX+'manifest.json'))},indent=2))

if __name__=='__main__':main()
