import argparse,hashlib,json,re
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    H=Path(__file__).resolve().parent
    def read(n):return json.loads((H/n).read_text())
    def pin(p,e):
        assert p.is_file() and p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],str(p)
    manifest=read('target-manifest.json')
    for e in manifest['files']:pin(H/e['path'],e)
    pins=read('target-source-pins.json')['files']
    for e in pins:
        pin(H/'inputs/root'/e['path'],e)
        if args.live:pin(args.root/e['path'],e)
    selected=read('target-selection.json')
    digest='7187a93a97be5cd1e1622e3945037b0c8fbb41b48a91b630c832fd054a61e804'
    assert selected['finalized'] and selected['source_sha256']==digest
    assert (selected['lean_jobs'],selected['failed_lean_checks'],selected['canonical_jobs'],selected['public_pairs'])==(3,0,1,1)
    assert selected['selected_strict']=='target-direct-1' and selected['selected_public']=='target-public-1'
    source=H/selected['source']
    text=source.read_text()
    assert sha(source)==digest and len(text.splitlines())==169
    assert re.findall(r'^theorem (\w+)',text,re.M)==['force_receipt']
    assert not re.search(r'^(?:structure|def|inductive|axiom)\s|\b(?:sorry|admit|native_decide)\b',text,re.M)
    public=text.split('theorem force_receipt',1)[1]
    assert 'requireAll' not in public and 'primary' not in public
    assert 'masks : ∀ index path, index :: path ∈ record.paths' in public
    assert 'known : Values base values' in public
    assert 'Ready formulas solver inventory record values base before' in public
    for fragment in ['SourceCurrentRawCorridorProjectionCap.forest projection.graph','SourceCurrentRequiredSharedTargetCap.Stored','SourceEqualityClassTarget.operandPaths_nonroot record coherent active','SourceCurrentConstrainedCapMemoMerge.retained Plain','SourceCurrentConstrainedCapCurrentNative.step (max headDepth tailDepth)','hit present => exact ⟨stored,stored.slots action value present⟩']:
        assert fragment in text,fragment
    for stem in ['target-direct-1','target-canonical-1','target-public-1']:
        receipt=read(stem+'.json')
        assert receipt['exit_code']==0
        assert sha(H/receipt['source'])==receipt['sha256']
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1]=='-Dlinter.all=true'
        assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
        assert read(receipt['limits'])=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=read(stem+'.usage.json')
        assert usage['age_seconds']<120 and usage['remaining_percent']>1
    for stem in ['target-direct-1','target-canonical-1']:
        assert not (H/(stem+'.log')).read_bytes()
        assert (H/(stem+'.source.lean')).read_bytes()==source.read_bytes()
    canonical=read('target-canonical-1.json')['command']
    assert '-R' in canonical and '-o' in canonical
    assert Path(canonical[-1]).name==source.name
    assert Path(canonical[canonical.index('-o')+1]).name==source.with_suffix('.olean').name
    assert (H/'target-canonical-1.input/MicroCFTA'/source.name).read_bytes()==source.read_bytes()
    for e in selected['artifacts']:pin(H/e['path'],e)
    head='MicroCFTA.SourceCurrentRawCorridorSharedTargetCap.force_receipt'
    printer=(H/'target-public-1.source.lean').read_text()
    assert printer==(H/'target-public.lean').read_text() and printer.startswith(text)
    for setting in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
        assert 'set_option '+setting in printer
    for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+head)==1
    log=(H/'target-public-1.log').read_text()
    assert len(log.encode())==selected['printer_bytes']==118723
    assert sha(H/'target-public-1.log')==selected['printer_sha256']=='998ca729aaa6d255e89b418d8f1acb9e8fa0e103c02f75624797e97e72eafe35'
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    assert '_private' not in log.split('@'+head+' :',1)[1].split('\ntheorem '+head,1)[0]
    reports=[{x.strip() for x in re.sub(r'\.\{[^}]*\}','',r).split(',')} for r in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)]
    assert reports==[{'propext','Classical.choice','Quot.sound'}]
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),'lean_jobs':3,'failed_lean_checks':0,'canonical_jobs':1,'public_pairs':1,'constructed_pairs':0}))
if __name__=='__main__':main()
