import argparse, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE='SourceCurrentClassCorridorChronology.lean'
HEADS=['MicroCFTA.SourceCurrentClassCorridorChronology.'+name for name in ['fold','pass','indexed_phase']]
def check(base,entry):
    data=(base/entry['path']).read_bytes()
    assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'chronology-manifest.json').read_text())
    for entry in manifest['files']: check(HERE,entry)
    for entry in manifest['sources']:
        check(HERE/'inputs/root',entry)
        if args.live: check(args.root,entry)
    assert json.loads((HERE/'chronology-source-pins.json').read_text())['files']==manifest['sources']
    selection=json.loads((HERE/'chronology-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads']==HEADS
    assert selection['lean_jobs']==len(selection['attempts'])==3
    assert selection['strict_jobs']==2 and selection['public_jobs']==1 and selection['canonical_jobs']==0
    assert selection['new_public_pairs']==3 and selection['constructed_pairs']==0
    assert selection['failed_checks']==1 and selection['warning_checks']==0
    assert not selection['unselected_successes']
    source=(HERE/SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest()==selection['source_sha256']
    assert source==(HERE/(selection['selected_strict']+'.source.lean')).read_text()
    assert len(source.splitlines())==197
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
    assert re.findall(r'^theorem (\w+)',source,re.M)==['fold','pass','indexed_phase']
    assert not re.search(r'^(?:def|inductive|structure) ',source,re.M)
    assert source.count('SourceCurrentClassEndpointCorridors.class_reads')==1
    assert source.count('SourceCurrentClassPassPhaseLineage.fold_indexed')==1
    assert 'SourceEqualityProjectionLanguage.all₂_signed' in source
    assert source.count('All₂ (fun original result => ∀ path, RawCorridor path original → RawCorridor path result)')==3
    assert 'receipt.domains _ (domains record List.mem_cons_self path member)' in source
    assert not re.search(r'\b(?:History|ClassTrace|primary|falsegate)\b',source)
    assert selection['failed_checks']==sum(code!=0 for code in selection['attempts'].values())
    for stem,exit_code in selection['attempts'].items():
        meta=json.loads((HERE/(stem+'.json')).read_text())
        assert meta['exit_code']==exit_code
        assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
        assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=json.loads((HERE/(stem+'.usage.json')).read_text())
        assert usage['age_seconds']<120 and usage['remaining_percent']>1
        assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
        assert '-Dlinter.all=true' in meta['command']
        assert meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
    assert not (HERE/(selection['selected_strict']+'.log')).read_bytes()
    failed=(HERE/'chronology-direct-1.log').read_text()
    assert failed.count('error: Application type mismatch')==2
    assert 'has type' in failed and 'but is expected' in failed
    printer=(HERE/(selection['selected_public']+'.source.lean')).read_text()
    assert printer.startswith(source)
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in printer
    log=(HERE/(selection['selected_public']+'.log')).read_text()
    assert len(log.encode())==selection['public_log_bytes']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    for index,head in enumerate(HEADS):
        for directive in ['#check @','#print ','#print axioms ']:
            assert printer.count(directive+head+'\n')==1
        axioms=re.search(r"'"+re.escape(head)+r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
        assert axioms,head
        names=set() if axioms.group(1) is None else set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',axioms.group(1)).strip()))
        assert names<={'propext','Classical.choice','Quot.sound'},(head,names)
        body=log.split('theorem '+head,1)[1].split("'"+head+"'",1)[0]
        typ,proof=body.split(':=',1)
        assert typ.strip() and proof.strip() and '_private' not in typ,head
    print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),'new_public_pairs':3,'constructed_pairs':0,'lean_jobs':3,'failed_checks':1,'warning_checks':0,'canonical_jobs':0,'live':args.live}))
if __name__=='__main__': main()
