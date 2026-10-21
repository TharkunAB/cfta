import argparse, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE='SourceCurrentTargetOperandPositivePosition.lean'
HEADS=['MicroCFTA.SourceCurrentTargetOperandPositivePosition.'+name for name in ['project','operand']]

def check(base,e):
    data=(base/e['path']).read_bytes()
    assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
    p.add_argument('--live',action='store_true')
    a=p.parse_args()
    m=json.loads((HERE/'target-position-manifest.json').read_text())
    for e in m['files']: check(HERE,e)
    for e in m['sources']:
        check(HERE/'inputs/root',e)
        if a.live: check(a.root,e)
    assert json.loads((HERE/'target-position-source-pins.json').read_text())['files']==m['sources']
    s=json.loads((HERE/'target-position-selection.json').read_text())
    assert s['finalized'] and s['public_heads']==HEADS
    assert s['lean_jobs']==len(s['attempts']) and s['canonical_jobs']==0
    assert s['new_public_pairs']==len(HEADS) and s['constructed_pairs']==0
    source=(HERE/SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest()==s['source_sha256']
    assert source==(HERE/(s['selected_strict']+'.source.lean')).read_text()
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
    assert len(re.findall(r'^theorem ',source,re.M))==2
    assert not re.search(r'^(?:def|inductive|structure) ',source,re.M)
    assert source.count('private def RowPosition')==1 and source.count('private def Relevant')==1
    assert 'Relevant row → accept row' in source
    assert 'SourceCurrentRequiredPositivePosition.not_plain positive' in source
    assert 'row_origin_position fields children ⟨child, chosen, rest⟩' in source
    actual=source.split('theorem operand ',1)[1]
    for text in ['SourceEqualityRequiredExecution.requireAll requiredFuel','SourceCurrentRequiredPrimaryExposure.selected_domain',
                 'SourceCurrentRequiredRowOrigins.children graph','SourceCurrentRequiredGuard.children Plain graph',
                 'SourceCurrentAllocatedTargetWorkerSound.projection_sound','SourceCurrentMergePositivePosition.allocated',
                 'SourceCurrentRequiredPrimaryExposure.false_class_paths','SourceCurrentRequiredPrimaryExposure.false_selected']:
        assert actual.count(text)==1,text
    assert 'sameHeap : before.native.machine.heap = preparedHeap' in actual
    assert 'originals[index]? = some original ∧ PositiveAt original (path ++ residual)' in actual
    assert s['lean_jobs']==4 and s['failed_checks']==2 and s['strict_jobs']==3 and s['public_jobs']==1
    assert sum(code!=0 for code in s['attempts'].values())==s['failed_checks']
    for name,code in s['attempts'].items():
        meta=json.loads((HERE/(name+'.json')).read_text())
        assert meta['exit_code']==code
        assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
        assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
        assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=json.loads((HERE/(name+'.usage.json')).read_text())
        assert usage['age_seconds']<120 and usage['remaining_percent']>1
        assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
        assert '-Dlinter.all=true' in meta['command']
        assert meta['command'][0].endswith('leanprover--lean4---v4.34.1/bin/lean')
    assert not (HERE/(s['selected_strict']+'.log')).read_bytes()
    printer=(HERE/(s['selected_public']+'.source.lean')).read_text()
    assert printer.startswith(source)
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in printer
    log=(HERE/(s['selected_public']+'.log')).read_text()
    assert len(log.encode())==s['public_log_bytes']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    for head in HEADS:
        for directive in ['#check @','#print ','#print axioms ']:
            assert printer.count(directive+head+'\n')==1
        block=re.search(r"'"+re.escape(head)+r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
        assert block,head
        names=set() if block.group(1) is None else set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',block.group(1)).strip()))
        assert names <= {'propext','Classical.choice','Quot.sound'},(head,names)
        body=log.split('theorem '+head,1)[1].split("'"+head+"'",1)[0]
        typ,proof=body.split(':=',1)
        assert typ.strip() and proof.strip() and '_private' not in typ,head
    print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'new_public_pairs':2,'constructed_pairs':0,'lean_jobs':4,'failed_checks':2,'canonical_jobs':0,'live':a.live}))
if __name__=='__main__': main()
