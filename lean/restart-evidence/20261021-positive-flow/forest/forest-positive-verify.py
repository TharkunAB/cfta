import argparse, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
HEAD='MicroCFTA.SourceCurrentRequiredForestPositive.requireAll'
SOURCE='SourceCurrentRequiredForestPositive.lean'

def check(base,e):
    data=(base/e['path']).read_bytes()
    assert len(data)==e['bytes'] and hashlib.sha256(data).hexdigest()==e['sha256'],e['path']

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'))
    p.add_argument('--live',action='store_true')
    a=p.parse_args()
    m=json.loads((HERE/'forest-positive-manifest.json').read_text())
    for e in m['files']: check(HERE,e)
    for e in m['sources']:
        check(HERE/'inputs/root',e)
        if a.live: check(a.root,e)
    assert json.loads((HERE/'forest-positive-source-pins.json').read_text())['files']==m['sources']
    s=json.loads((HERE/'forest-positive-selection.json').read_text())
    assert s['finalized'] and s['public_heads']==[HEAD]
    assert s['lean_jobs']==3 and s['failed_checks']==1 and s['canonical_jobs']==0
    assert s['new_public_pairs']==1 and s['constructed_pairs']==0
    source=(HERE/SOURCE).read_text()
    assert hashlib.sha256(source.encode()).hexdigest()==s['source_sha256']
    assert source==(HERE/'forest-positive-direct-2.source.lean').read_text()
    assert len(source.splitlines())==60 and source.count('theorem requireAll ')==1
    assert not re.search(r'\bsorry\b|\badmit\b|native_decide|trustCompiler',source)
    assert source.count('SourceCurrentRequiredPrimaryExposure.selected_domain')==1
    assert source.count('SourceCurrentRequiredRowOrigins.children graph')==1
    assert source.count('SourceEqualityProjectionLanguage.all₂_selected related index output found')==1
    assert source.count('SourceCurrentRequiredPositivePosition.origin origin positive')==1
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
    assert not (HERE/'forest-positive-direct-2.log').read_bytes()
    failed=(HERE/'forest-positive-direct-1.log').read_text()
    assert 'Application type mismatch' in failed and 'instDecidableEqEdgeKeyLabelFormulaConstraint' in failed
    printer=(HERE/'forest-positive-public-1.source.lean').read_text()
    assert printer.startswith(source)
    for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+option in printer
    for directive in ['#check @','#print ','#print axioms ']:
        assert printer.count(directive+HEAD+'\n')==1
    log=(HERE/'forest-positive-public-1.log').read_text()
    assert len(log.encode())==s['public_log_bytes']
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    report=re.search(r'depends on axioms:\s*\[([^\]]*)\]',log)
    assert report
    names=set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report.group(1)).strip()))
    assert names <= {'propext','Classical.choice','Quot.sound'},names
    body=log.split('theorem '+HEAD,1)[1].split("'"+HEAD+"'",1)[0]
    typ,proof=body.split(':=',1)
    assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'new_public_pairs':1,'constructed_pairs':0,'lean_jobs':3,'failed_checks':1,'canonical_jobs':0,'live':a.live}))

if __name__=='__main__': main()
