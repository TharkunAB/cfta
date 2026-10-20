import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent

def pin(base,item):
    b=(base/item['path']).read_bytes()
    assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));p.add_argument('--live',action='store_true');a=p.parse_args()
    manifest=json.loads((HERE/'math-review-manifest.json').read_text())['files']
    roots=json.loads((HERE/'math-review-source-pins.json').read_text())['files']
    for x in manifest:pin(HERE,x)
    for x in roots:pin(a.root,x)
    sel=json.loads((HERE/'math-review-selection.json').read_text())
    assert sel['finalized'] and sel['new_lean_jobs']==sel['owned_pairs']==sel['reused_constructed_pairs']==0
    assert sel['reused_public_pairs']==1 and sel['reused_selected_jobs']==3
    source=(HERE/'SourceCurrentAllocatedRecursivePrefixScope.lean').read_bytes()
    assert source==(a.root/'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixScope.lean').read_bytes()
    assert len(re.findall(r'^theorem ',source.decode(),re.M))==1
    for job in sel['jobs']:
        stem=job['stem'];m=json.loads((HERE/(stem+'.json')).read_text())
        assert m['exit_code']==0
        assert m['wrapper'][m['wrapper'].index('--mem')+1]=='4G'
        assert m['wrapper'][m['wrapper'].index('--time')+1]=='5m'
        assert json.loads((HERE/m['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=json.loads((HERE/(stem+'.usage.json')).read_text());assert usage['remaining_percent']>1 and usage['age_seconds']<120
        log=(HERE/(stem+'.log')).read_text()
        if job['kind']=='strict':
            assert not log and (HERE/(stem+'.source.lean')).read_bytes()==source
        elif job['kind']=='canonical':
            assert 'Build completed successfully' in log and not re.search(r'\berror:',log)
            assert m['command'][-2:]==['build','MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope']
            assert all(w=='MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.' for w in re.findall(r'^warning: (.+)$',log,re.M))
        else:
            printer=(HERE/(stem+'.source.lean')).read_text();assert printer.startswith(source.decode())
            for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:assert 'set_option '+option in printer
            head='MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope.node_scope'
            for prefix in ['#check @','#print ','#print axioms ']:assert prefix+head in printer
            assert len(re.findall(r'^#print (?!axioms )',printer,re.M))==1
            assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
            reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
            assert len(reports)+len(re.findall('does not depend on any axioms',log))==1
            for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
        if job['kind']!='canonical':
            assert m['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean' and '-Dlinter.all=true' in m['command']
            assert hashlib.sha256((HERE/m['source']).read_bytes()).hexdigest()==m['sha256']
        if a.live:
            base=a.root/'lean/restart-evidence/20261020-native-owner-capture-ancestry'/job['location']
            for ext in ['.json','.log','.limits.json','.usage.json']+([] if job['kind']=='canonical' else ['.source.lean']):assert (HERE/(stem+ext)).read_bytes()==(base/(stem+ext)).read_bytes()
    print(json.dumps({'status':'PASS','pins':len(manifest)+len(roots),'new_lean_jobs':0,'owned_pairs':0,'reused_public_pairs':1,'reused_constructed_pairs':0,'reused_selected_jobs':3,'mode':'live' if a.live else 'ordinary'}))
if __name__=='__main__':main()
