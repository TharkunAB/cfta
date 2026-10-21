#!/usr/bin/env python3
"""Verify frozen outer store proof evidence without running Lean."""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts,value
    return path


def check(path: Path,pin: dict) -> None:
    assert path.is_file() and path.stat().st_size==pin['bytes'] and digest(path)==pin['sha256'],str(path)


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    manifest=read(here/'outer-native-stores-manifest.json')
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here/relative(pin['path']),pin)
    sources=read(here/'outer-native-stores-source-pins.json')['files']
    assert sources==manifest['sources']
    for pin in sources:
        check(here/'inputs/root'/relative(pin['path']),pin)
        if args.live:
            check(args.root/relative(pin['path']),pin)
    selected=read(here/'outer-native-stores-selection.json')
    assert selected['finalized'] and selected['canonical_jobs']==selected['constructed_pairs']==0
    source=here/selected['source']
    assert digest(source)==selected['source_sha256']
    assert len(source.read_text().splitlines())==selected['source_lines']
    text=source.read_text()
    assert re.findall(r'^theorem (\w+)',text,re.M)==['edge_call','node_call','descendants']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b',text)
    if args.live:
        assert (args.root/'lean/MicroCFTA'/source.name).read_bytes()==source.read_bytes()
    assert selected['new_public_pairs']==3 and selected['public_headers_match_frozen_proposal']
    proposal=(here/'inputs/proposed-signature.lean.txt').read_text()
    for name in ['edge_call','node_call','descendants']:
        header='theorem '+name+'\n'+text.split('theorem '+name+'\n',1)[1].split(' := by',1)[0]
        expected=('theorem '+name+'\n'+proposal.split('theorem '+name+'\n',1)[1]).split('\n\n',1)[0].split('\nend MicroCFTA.',1)[0].rstrip()
        assert header==expected,name
    ledger=read(here/'outer-native-stores-attempt-ledger.json')['attempts']
    assert len(ledger)==len({item['name'] for item in ledger})==selected['lean_jobs']
    failed=warned_success=0
    for item in ledger:
        stem=item['name'];receipt=read(here/(stem+'.json'))
        assert item['lean_launched'] and receipt['exit_code']==item['exit_code']
        assert digest(here/receipt['source'])==receipt['sha256']
        assert receipt['source']==stem+'.source.lean' and receipt['log']==stem+'.log'
        assert read(here/(stem+'.limits.json'))=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=read(here/(stem+'.usage.json'))
        assert 0<=usage['age_seconds']<120 and usage['remaining_percent']>1
        assert '--mem' in receipt['wrapper'] and '4G' in receipt['wrapper'] and '--time' in receipt['wrapper'] and '5m' in receipt['wrapper']
        assert '-Dlinter.all=true' in receipt['command']
        content=(here/(stem+'.log')).read_text()
        assert item['warning_diagnostics']==len(re.findall(r': warning:',content))
        failed+=receipt['exit_code']!=0
        warned_success+=receipt['exit_code']==0 and item['warning_diagnostics']>0
    assert failed==selected['failed_checks'] and warned_success==selected['warning_success_checks']
    strict=selected['selected_strict'];public=selected['selected_public']
    assert read(here/(strict+'.json'))['exit_code']==read(here/(public+'.json'))['exit_code']==0
    assert (here/(strict+'.log')).stat().st_size==0
    assert (here/(strict+'.source.lean')).read_bytes()==source.read_bytes()
    full=here/(public+'.log')
    assert full.stat().st_size==selected['public_log_bytes'] and digest(full)==selected['public_log_sha256']
    log=full.read_text()
    assert not re.search(r'error:|error\(|warning:|maximum recursion depth|failed to pretty.print|\(truncated\)|\.\.\.|⋯|…',log,re.I)
    printed=(here/(public+'.source.lean')).read_text()
    assert printed.startswith(text+'\n')
    for option in ['pp.explicit','pp.fullNames','pp.proofs','pp.universes','pp.deepTerms']:
        assert 'set_option '+option+' true' in printed
    assert 'set_option pp.proofs.threshold 254' in printed and 'set_option pp.maxSteps 10000000' in printed
    assert 'set_option maxRecDepth 30000' in printed
    for head in selected['public_heads']:
        checked,declared=log.split('@'+head+' :',1)[1].split('\ntheorem '+head,1)
        declared,proof=declared.split(' :=',1)
        assert ''.join(checked.split())==''.join(declared.removeprefix(' :').split()),head
        assert '_private' not in checked+declared and 'Stores' not in checked+declared
        assert len(proof)>100,head
        match=re.search(re.escape("'"+head+"' depends on axioms:")+r'\s*\[([^\]]*)\]',log)
        assert match,head
        names=sorted(part.strip() for part in re.sub(r'\.\{[^}]*\}','',match.group(1)).split(','))
        assert names==selected['axioms_by_head'][head]==['Classical.choice','Quot.sound','propext'],(head,names)
        assert printed.count('#check @'+head+'\n')==printed.count('#print '+head+'\n')==printed.count('#print axioms '+head+'\n')==1
    assert read(here/'prelaunch-mechanical-delta.json')['lean_commands']==0
    assert (here/'outer-native-stores-prelaunch-1.source.lean').read_bytes()==(here/'inputs/prelaunch-reviewed-521.lean').read_bytes()
    assert selected['infrastructure_attempts']==0 and selected['prelaunch_proof_commands']==0
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),
        'root_pins':len(sources),'lean_jobs':len(ledger),'failed_checks':failed,
        'warning_success_checks':warned_success,'canonical_jobs':0,'constructed_pairs':0,
        'public_heads':selected['public_heads'],'axioms_by_head':selected['axioms_by_head'],
        'manifest_sha256':digest(here/'outer-native-stores-manifest.json')},indent=2))


if __name__=='__main__':
    main()
