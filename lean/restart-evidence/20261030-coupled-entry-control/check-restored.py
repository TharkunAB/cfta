from pathlib import Path
import hashlib,json,subprocess
ROOT=Path('/home/tritlo/Code/mcfta');AREA=Path('/tmp/mcfta-coupled-entry-control-restored-20261030')
OUT=Path('/tmp/mcfta-coupled-entry-control-packaging-20261030');SNAP=ROOT/'lean/restart-evidence/20261030-coupled-entry-control'
result=subprocess.run(['python3',str(SNAP/'verify.py'),str(SNAP),'--extract',str(AREA)],check=True,stdout=subprocess.PIPE,text=True)
(OUT/'reconstruct.json').write_text(result.stdout)
validation=OUT/'restored-validation';validation.mkdir()
for name in ['verify-current.py','verify-owned.py']:
    result=subprocess.run(['python3',str(AREA/name),str(AREA),str(validation)],check=True,stdout=subprocess.PIPE,text=True)
    (OUT/(name+'.log')).write_text(result.stdout)
assert json.loads((validation/'verification-summary.json').read_text())==json.loads((AREA/'verification-summary.json').read_text())
assert json.loads((validation/'owned-bundle-verification.json').read_text())==json.loads((AREA/'owned-bundle-verification.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
for name,count,copydir in [('final-strong-sources.json',518,'final-strong-inputs'),('final-lean-sources.json',4717,None),('final-haskell.json',835,'final-haskell-inputs'),('final-documents.json',4,'final-documents')]:
    rows=json.loads((AREA/name).read_text());assert len(rows)==count
    for row in rows:
        b=(ROOT/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256']
        if copydir:assert b==(AREA/copydir/row['path']).read_bytes()
for name in ['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md']:
    assert (AREA/'final-documents'/name).read_bytes().endswith((AREA/'prior-documents'/name).read_bytes())
seal=json.loads((AREA/'FROZEN.json').read_text());assert seal['write_halt'] and seal['full_goal']=='active'
for p in AREA.rglob('*'):
    if p.is_file():p.chmod(0o444)
for p in sorted([p for p in AREA.rglob('*') if p.is_dir()],reverse=True):p.chmod(0o555)
AREA.chmod(0o555)
report={'status':'pass','payloads':len(seal['payloads'])+1,'lean':4717,'protected':518,'haskell':835,'documents':4,'strict_current':6,'input_snapshots':143,'old_document_suffixes':3,'reconstructed_write_halt':True,'full_goal':'active'}
(OUT/'restored-current-matches.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
