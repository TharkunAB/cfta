from pathlib import Path
import hashlib,json
out=Path(__file__).resolve().parent

def sha(b): return hashlib.sha256(b).hexdigest()
def checked_record(r):
 p=out/r['path']; b=p.read_bytes(); assert len(b)==r['bytes'] and sha(b)==r['sha256'],str(p); return b
idx=json.loads((out/'source-index.json').read_text())
for r in idx['sources']:
 whole=checked_record(r['whole']); lines=whole.splitlines(keepends=True)
 assert Path(r['source']).read_bytes()==whole,r['source']
 for c in r['cuts']:
  cut=checked_record(c); assert cut==b''.join(lines[c['first_line']-1:c['last_line']]),c['path']
inv=json.loads((out/'documents/inverse-independent.json').read_text())
for r in inv['documents']:
 prior=checked_record(r['prior']); insert=checked_record(r['insert']); current=checked_record(r['current']); n=r['insert']['offset']
 assert current==prior[:n]+insert+prior[n:]
 assert current[:n]+current[n+len(insert):]==prior
checked_record(inv['note'])
sv=json.loads((out/'final-evidence/source-validation.json').read_text())
reports=[]
for r in sv['commands']:
 folder=out/'checks'/r['folder']; report=json.loads((folder/'report.json').read_text()); raw=(folder/'raw.log').read_bytes()
 assert report['exit_code']==r['exit_code'] and len(raw)==r['bytes']==report['bytes'] and sha(raw)==r['sha256']==report['sha256']
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if 'source_sha256' in report:
  actual=Path(report['command'][-1]); original=Path('/tmp/mcfta-prepared-origins-20261028')/r['folder']
  p=folder/actual.relative_to(original)
  assert sha(p.read_bytes())==report['source_sha256'],str(p)
 reports.append(report)
pv=json.loads((out/'final-evidence/public-validation.json').read_text())
public=(out/'checks/public-readback-final/raw.log').read_bytes(); prior=(out/'checks/prior-public-readback/raw.log').read_bytes(); appendix=(out/'final-evidence/new-public-blocks.txt').read_bytes()
assert len(public)==pv['bytes'] and sha(public)==pv['sha256'] and len(prior)==pv['prior_bytes']
assert public==prior+appendix and len(appendix)==pv['new_bytes'] and sha(appendix)==pv['new_sha256']
reviewed=json.loads((out/'public-reviewed-index.json').read_text())['reviewed']
for r in reviewed:
 b=checked_record(r); assert appendix[r['offset']:r['offset']+r['bytes']]==b
 assert b''.join(appendix.splitlines(keepends=True)[r['first_line']-1:r['last_line']])==b
for r in json.loads((out/'old-contract-comparison-v1.json').read_text())['comparisons']:
 old=(out/r['original_path']).read_bytes(); recovered=(out/r['recovered_path']).read_bytes()
 assert old==recovered and len(old)==r['bytes'] and sha(old)==r['sha256']
mods=json.loads((out/'final-evidence/modules.json').read_text())
for m in mods:
 source=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')/(m+'.lean')
 assert sha(source.read_bytes())==sv['source_hashes'][m]
result={'status':'PASS','source_wholes':len(idx['sources']),'source_line_cuts':sum(len(r['cuts'])for r in idx['sources']),'document_inverses':len(inv['documents']),'whole_printed_blocks_reviewed':len(reviewed),'whole_printed_bytes_reviewed':sum(r['bytes']for r in reviewed),'copied_command_reports':len(reports),'current_commands':sv['current_commands'],'inherited_commands':sv['inherited_commands'],'current_failures':sv['failures'],'old_full_declaration_recoveries':2,'owned_modules_unchanged_after_first_strict_pass':True,'source_checkpoint':(out/'final-evidence/source-head.txt').read_text().strip()}
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
