import argparse, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE='SourceCurrentRequiredRawCorridor.lean'
HEADS=['MicroCFTA.SourceCurrentRequiredRawCorridor.'+name for name in ['RawCorridor','origin','original_gate','required']]
def check(base,entry):
    data=(base/entry['path']).read_bytes()
    assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=json.loads((HERE/'raw-corridor-manifest.json').read_text())
    for entry in manifest['files']: check(HERE,entry)
    for entry in manifest['sources']:
        check(HERE/'inputs/root',entry)
        if args.live: check(args.root,entry)
    assert json.loads((HERE/'raw-corridor-source-pins.json').read_text())['files']==manifest['sources']
    selection=json.loads((HERE/'raw-corridor-selection.json').read_text())
    assert selection['finalized'] and selection['public_heads']==HEADS
    assert selection['lean_jobs']==len(selection['attempts'])==4
    assert selection['strict_jobs']==2 and selection['public_jobs']==1 and selection['canonical_jobs']==1
    assert selection['new_public_pairs']==4 and selection['constructed_pairs']==0
    assert selection['failed_checks']==0 and selection['warning_checks']==1
    assert selection['unselected_successes']==['raw-corridor-direct-1']
    source=(HERE/SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest()==selection['source_sha256']
    assert source==(HERE/(selection['selected_strict']+'.source.lean')).read_text()
    assert len(source.splitlines())==220
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
    assert re.findall(r'^theorem (\w+)',source,re.M)==['origin','original_gate','required']
    assert re.findall(r'^inductive (\w+)',source,re.M)==['RawCorridor']
    assert '(bounded : ∃ depth, Cap Plain depth value) : RawCorridor path value' in source
    assert source.count('SourceCurrentRequiredRowOrigins.children')==1
    assert 'SourceCurrentRequiredPrimaryExposure.false_edges_members' in source
    assert 'SourceCurrentRequiredPrimaryExposure.false_selected' in source
    assert 'originals[index]? = some original ∧ Origin original value ∧' in source
    assert '∃ depth, Cap Plain depth value' in source
    assert not re.search(r'\b(?:readAll_caps|union_finite|project_corridor|ProjectRows|Keeps|Stored|Support)\b',source)
    assert '(closed :' not in source
    for stem,exit_code in selection['attempts'].items():
        meta=json.loads((HERE/(stem+'.json')).read_text())
        assert meta['exit_code']==exit_code==0
        assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
        assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=json.loads((HERE/(stem+'.usage.json')).read_text())
        assert usage['age_seconds']<120 and usage['remaining_percent']>1
        assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
        assert '-Dlinter.all=true' in meta['command']
        assert meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
    for stem in [selection['selected_strict'],selection['selected_canonical']]:
        assert not (HERE/(stem+'.log')).read_bytes()
    warnings=(HERE/'raw-corridor-direct-1.log').read_text()
    assert warnings.count('warning: missing doc string for public constructor')==2
    assert not re.search(r'\berror(?:\([^)]*\))?:',warnings)
    canonical=json.loads((HERE/(selection['selected_canonical']+'.json')).read_text())
    assert '-R' in canonical['command'] and '-o' in canonical['command']
    assert (HERE/canonical['source']).read_text()==source
    assert Path(canonical['source']).name==SOURCE
    assert (HERE/'import-tree/MicroCFTA/SourceCurrentRequiredRawCorridor.olean').stat().st_size>0
    timeout=json.loads((HERE/'raw-corridor-tool-timeout.json').read_text())
    assert not timeout['launched'] and timeout['lean_jobs_added']==0
    assert timeout['classification']=='permission_review_timeout'
    assert 'did not finish before its deadline' in timeout['message']
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
        body=log.split(('inductive ' if index==0 else 'theorem ')+head,1)[1].split("'"+head+"'",1)[0]
        if index==0:
            assert 'constructors:' in body and head+'.full' in body and head+'.node' in body
            assert '_private' not in body
        else:
            typ,proof=body.split(':=',1)
            assert typ.strip() and proof.strip() and '_private' not in typ,head
    print(json.dumps({'status':'PASS','pins':len(manifest['files'])+len(manifest['sources']),'new_public_pairs':4,'constructed_pairs':0,'lean_jobs':4,'failed_checks':0,'warning_checks':1,'canonical_jobs':1,'tool_timeouts_before_launch':1,'live':args.live}))
if __name__=='__main__': main()
