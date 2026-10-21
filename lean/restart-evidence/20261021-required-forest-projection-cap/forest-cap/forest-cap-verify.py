import argparse, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE='SourceCurrentRequiredForestProjectionCap.lean'
HEADS=['MicroCFTA.SourceCurrentRequiredForestProjectionCap.'+name for name in ['project']]

def check(base,e):
    data=(base/e['path']).read_bytes()
    assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
    p.add_argument('--live',action='store_true')
    a=p.parse_args()
    m=json.loads((HERE/'forest-cap-manifest.json').read_text())
    for e in m['files']: check(HERE,e)
    for e in m['sources']:
        check(HERE/'inputs/root',e)
        if a.live: check(a.root,e)
    assert json.loads((HERE/'forest-cap-source-pins.json').read_text())['files']==m['sources']
    s=json.loads((HERE/'forest-cap-selection.json').read_text())
    assert s['finalized'] and s['public_heads']==HEADS
    assert s['lean_jobs']==len(s['attempts']) and s['canonical_jobs']==0
    assert s['infrastructure_attempts']==['forest-cap-direct-1']
    ledger=json.loads((HERE/'forest-cap-attempts.json').read_text())
    assert ledger['actual_lean_jobs']==2 and ledger['infrastructure_attempts']==1
    assert [e['stem'] for e in ledger['entries'] if e['launched']]==list(s['attempts'])
    infra=ledger['entries'][0]
    assert infra['stem']=='forest-cap-direct-1' and not infra['launched']
    assert infra['classification']=='infrastructure_bus_denial'
    for key in ['receipt','log']:
        check(HERE,infra[key])
    assert json.loads((HERE/infra['receipt']['path']).read_text())['exit_code']==1
    assert (HERE/infra['log']['path']).read_text()=='Failed to connect to bus: Operation not permitted\n'
    assert not (HERE/'forest-cap-direct-1.limits.json').exists()
    assert s['new_public_pairs']==len(HEADS) and s['constructed_pairs']==0
    source=(HERE/SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest()==s['source_sha256']
    assert source==(HERE/(s['selected_strict']+'.source.lean')).read_text()
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
    assert len(re.findall(r'^theorem ',source,re.M))==1
    assert not re.search(r'^(?:def|inductive|structure) ',source,re.M)
    assert source.count('SourceCurrentOriginalGateProjectionCap.project')==1
    assert source.count('SourceCurrentRequiredRowOrigins.children')==1
    assert source.count('later.available value (requiredEffects.2.2.2.2 value member)')==1
    assert 'later : Keeps preparedHeap currentHeap' in source
    assert 'actual : Forest ((index :: path).map Int.ofNat) prepared currentHeap result afterHeap' in source
    assert '∃ depth, Cap Plain depth result' in source
    assert source.count('SourceCurrentRequiredUnionNormal.UnionNormal scanHeap')==1
    assert 'UnionNormal currentHeap' not in source
    assert not re.search(r'\b(?:PositiveAt|Stored|Support|closed|sameHeap)\b',source)
    assert s['strict_jobs']+s['public_jobs']==s['lean_jobs']
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
    print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'new_public_pairs':1,'constructed_pairs':0,'lean_jobs':s['lean_jobs'],'failed_checks':s['failed_checks'],'canonical_jobs':0,'live':a.live}))
if __name__=='__main__': main()
