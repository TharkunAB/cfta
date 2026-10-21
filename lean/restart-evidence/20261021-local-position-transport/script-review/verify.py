import argparse,ast,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent

def sha(b):return hashlib.sha256(b).hexdigest()
def check(base,e,path=None):
 b=(base/(path or e['path'])).read_bytes()
 assert len(b)==e['bytes'] and sha(b)==e['sha256'],path or e['path']
 return b

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));p.add_argument('--live',action='store_true');a=p.parse_args()
 m=json.loads((HERE/'manifest.json').read_text());assert m['finalized']
 for e in m['files']:check(HERE,e)
 pins=json.loads((HERE/'source-pins.json').read_text())
 scripts={}
 for e in pins['sources']:
  b=check(HERE,e,e['snapshot'])
  if e['path'].endswith('.py'):ast.parse(b,filename=e['path']);scripts[Path(e['path']).name]=b.decode()
  if a.live:check(a.root,e)
 candidate=pins['external_candidate'];data=check(HERE,candidate,candidate['snapshot']);ast.parse(data)
 if a.live and Path(candidate['original_path']).exists():assert Path(candidate['original_path']).read_bytes()==data
 audit=next((HERE/e['snapshot']).read_text() for e in pins['sources'] if e['path']=='lean/MicroCFTA/Audit.lean')
 for module in ['SourceCurrentNativeMaybeMuPositivePositions','SourceCurrentTargetOperandPositivePosition']:
  line='import MicroCFTA.'+module+'\n';assert audit.count(line)==1 and audit.index(line)<audit.index('run_cmd do')
 assert 'AUDIT_DEPENDENCIES_PENDING' not in scripts['verify-checkpoint.py']
 for token in ["audit_source.index(line)<audit_source.index('run_cmd do')",'3563','74623','json.dumps(receipt, sort_keys=True)',"'previous-publication-support' in path.parts"]:
  assert token in scripts['verify-checkpoint.py'],token
 assert "replace(marker, line + marker, 1)" in scripts['publish-proof.py']
 for token in ["'git','add','-f'",'relative in index_names','assert index==head_entries',"assert not git('status','--porcelain')",'verify-seal.py']:
  assert token in data.decode(),token
 for token in ['starting-files.json','set(changed)==set(docs+','starting-stashes.txt','starting-worktrees.txt',"assert hs==",'assert active==']:
  assert token in scripts['verify-preservation.py'],token
 receipts=[]
 for e in json.loads((HERE/'receipt-accounting.json').read_text()):
  x=json.loads((HERE/e['snapshot']).read_text());assert Path(x['command'][0]).name in ['lean','lake'];receipts.append(json.dumps(x,sort_keys=True))
 assert len(set(receipts))==14 and sum(json.loads(k)['exit_code']!=0 for k in set(receipts))==7
 certificates=json.loads((HERE/'document-certificates.json').read_text());assert len(certificates)==9
 if a.live:
  for e in certificates:
   b=(a.root/e['path']).read_bytes();assert len(b)==e['current_bytes'] and sha(b)==e['current_sha256'],e['path']
   block=(HERE/e['inserted_block']).read_bytes()+b'\n';assert b.count(block)==1
   old=b.replace(block,b'',1);assert len(old)==e['baseline_bytes'] and sha(old)==e['baseline_sha256'],e['path']
  assert (a.root/'FINDINGS.md').read_bytes().startswith(b'# Current formalization findings\n\n## Haskell fix handoff for external work\n')
 print(json.dumps({'status':'PASS','live':a.live,'pins':len(m['files']),'owned_lean_lake_commands':0,'owned_public_pairs':0,'material_issues':0,'distinct_reused_lean_lake_commands':14,'retained_nonzero_commands':7,'document_byte_insertions':9,'audit_imports_before_command':True,'publication_executed_by_review':False}))
if __name__=='__main__':main()
