#!/usr/bin/env python3
"""Verify the selected-certificate source and all retained proof attempts."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path
PREFIX='selected-certificates-'
HEAD='MicroCFTA.SourceCurrentActualParentSelectedCertificates.selected_certificates'
def sha(path:Path)->str: return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path:Path)->dict: return json.loads(path.read_text())
def relative(value:str)->Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path

def check(path:Path,pin:dict)->None:
    assert path.is_file() and path.stat().st_size==pin['bytes'] and sha(path)==pin['sha256'],str(path)
def instant(value:str)->datetime.datetime: return datetime.datetime.fromisoformat(value.replace('Z','+00:00'))
def main()->None:
    parser=argparse.ArgumentParser();parser.add_argument('--root',required=True,type=Path);parser.add_argument('--live',action='store_true');args=parser.parse_args()
    here=Path(__file__).resolve().parent
    manifest=read(here/(PREFIX+'manifest.json')); assert manifest['finalized']
    for pin in manifest['files']: check(here/relative(pin['path']),pin)
    pins=read(here/(PREFIX+'source-pins.json'))['files'];assert pins==manifest['sources']
    for pin in pins:
        snapshot=here/relative(pin['snapshot']);check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end'];assert 1<=lo<=hi<=len(lines)
            assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()==span['sha256']
        if args.live: check(args.root/relative(pin['path']),pin)
    selected=read(here/(PREFIX+'selection.json'));assert selected['finalized']
    assert selected['public_heads']==[HEAD] and selected['canonical_jobs']==selected['constructed_pairs']==0
    assert selected['new_public_pairs']==1 and not selected['official_edits']
    source=here/relative(selected['source']);assert sha(source)==selected['source_sha256']
    text=source.read_text();assert len(text.splitlines())==selected['source_lines']
    assert re.findall(r'^theorem (\w+)',text,re.M)==['selected_certificates']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b',text)
    original=here/(PREFIX+'source-only.lean')
    assert sha(original)=='e1ea8ea5ce1e4839dd70da0527824e81c552385948a92a99ff99fc6ae976cbe6'
    public='theorem selected_certificates'+text.split('theorem selected_certificates',1)[1].split(' := by',1)[0]+'\n'
    assert public==(here/(PREFIX+'corrected-signature.lean.txt')).read_text()
    assert 'savedFourth = scanFourth ∧ HEq numeric.actual' in public
    assert '(current :' not in public and '(ranges :' not in public
    assert 'Retained trace records kept' in public and 'PassReads formulas solver pass preparedMemos final' in public
    assert text.count('SourceCurrentActualParentScanNativeStores.selected_scan formulas')==1
    assert 'SourceCurrentActualParentSemanticReads.parent formulas' not in text
    assert text.count('SourceCurrentScanNumeric.complete formulas')==1
    assert 'SourceCurrentConjunctionClassScanSoundness.verified' not in text
    if args.live:
        installed=args.root/'lean/MicroCFTA'/source.name
        if installed.exists(): assert sha(installed)==selected['source_sha256']
    ledger=read(here/(PREFIX+'attempt-ledger.json'))['attempts']
    assert len(ledger)==sum(item['lean_launched'] for item in ledger)==selected['lean_jobs']
    assert {item['name']:item['exit_code'] for item in ledger}==selected['attempts']
    assert sum(item['exit_code']!=0 for item in ledger)==selected['failed_checks']
    warning_jobs=0
    for item in ledger:
        stem=item['name'];receipt=read(here/(stem+'.json'));log_path=here/(stem+'.log')
        assert sha(here/(stem+'.json'))==item['receipt_sha256'] and sha(log_path)==item['log_sha256']
        assert item['kind']=='lean' and item['lean_launched'] and receipt['exit_code']==item['exit_code']
        assert sha(here/relative(receipt['source']))==receipt['sha256']
        assert receipt['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert receipt['command'][1]=='-Dlinter.all=true'
        assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
        assert read(here/relative(receipt['limits']))=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=read(here/(stem+'.usage.json'));assert usage['age_seconds']<120 and usage['remaining_percent']>1
        start,end=instant(receipt['started_at']),instant(receipt['observed_at'])
        assert 0<=(start-instant(usage['observed_at'])).total_seconds()<120
        assert 0<=(end-start).total_seconds()<300
        warning_jobs+=int(bool(re.search(r'\bwarning(?:\([^)]*\))?:',log_path.read_text())))
    assert selected['warning_checks']==warning_jobs and selected['infrastructure_attempts']==0
    strict=selected['selected_strict'];assert read(here/(strict+'.json'))['exit_code']==0
    assert (here/(strict+'.log')).stat().st_size==0
    assert (here/(strict+'.source.lean')).read_bytes()==source.read_bytes()
    stem=selected['selected_public'];assert read(here/(stem+'.json'))['exit_code']==0
    printer=(here/(stem+'.source.lean')).read_text()
    assert printer==(here/(PREFIX+'public.lean')).read_text() and printer.startswith(text)
    for option in ['pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000','linter.all true']:
        assert printer.count('set_option '+option)==1
    for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+HEAD)==1
    log_path=here/(stem+'.log');assert log_path.stat().st_size==selected['public_log_bytes'] and sha(log_path)==selected['public_log_sha256']
    log=log_path.read_text();assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    checked,theorem=log.split('@'+HEAD+' :',1)[1].split('\ntheorem '+HEAD,1)
    declared,proof=theorem.split(' :=',1)
    assert '_private' not in checked+declared and len(proof)>1000
    assert ''.join(checked.split())==''.join(declared.removeprefix(' :').split())
    report=re.search(re.escape("'"+HEAD+"' depends on axioms:")+r'\s*\[([^\]]*)\]',log);assert report
    axioms={part.strip() for part in re.sub(r'\.\{[^}]*\}','',report.group(1)).split(',')}
    assert axioms=={'propext','Classical.choice','Quot.sound'} and sorted(axioms)==selected['axioms_by_head'][HEAD]
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),'lean_jobs':selected['lean_jobs'],'failed_checks':selected['failed_checks'],'warning_checks':warning_jobs,'infrastructure_attempts':0,'canonical_jobs':0,'public_pairs':1,'constructed_pairs':0,'axioms_by_head':selected['axioms_by_head'],'manifest_sha256':sha(here/(PREFIX+'manifest.json'))},indent=2))
if __name__=='__main__':main()
