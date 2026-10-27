from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-flat-native-terminal-20261027')
def digest(data):return hashlib.sha256(data).hexdigest()
records=[item for item in json.loads((area/'strict-source-validation.json').read_text()) if item['module']!='Audit']
data=(root/'lean/MicroCFTA/Audit.lean').read_bytes()
records.append({'module':'Audit','strict_run':'strict-audit-1','bytes':len(data),'sha256':digest(data)})
for item in records:
 live=(root/'lean/MicroCFTA'/(item['module']+'.lean')).read_bytes()
 checked=(area/item['strict_run']/'MicroCFTA'/(item['module']+'.lean')).read_bytes()
 report=json.loads((area/item['strict_run']/'report.json').read_text())
 assert live==checked and digest(live)==item['sha256']==report['source_sha256'],item
 assert report['exit_code']==0
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if item['module']!='Audit':assert not re.search(rb'\b(sorry|admit|axiom|native_decide)\b|set_option\s+maxHeartbeats',live)
(area/'strict-source-validation.json').write_text(json.dumps(records,indent=2)+'\n')
public=(area/'installed-public-1/raw.log').read_bytes()
assert len(public)==242903 and digest(public)=='20a4bde110ca089aedb2be0a2bf2b58c981cb734e475552e7a1c28518a84006d'
axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",public.decode())
free=re.findall(r"'([^']+)' does not depend on any axioms",public.decode())
assert len(axioms)==12 and len(free)==0
assert {name for name,_ in axioms}=={'MicroCFTA.'+name for name in json.loads((area/'public-declarations.json').read_text())}
for _,group in axioms:assert set(re.split(r',\s*',group))<={'propext','Classical.choice','Quot.sound'}
for name in json.loads((area/'public-definitions.json').read_text()):
 assert re.search(r'^def MicroCFTA\.'+re.escape(name)+r'\b',public.decode(),re.M),name
prior=(area/'prior-audit.lean').read_bytes()
stripped=data
for name in json.loads((area/'modules.json').read_text()):stripped=stripped.replace(('import MicroCFTA.'+name+'\n').encode(),b'')
assert stripped==prior
(area/'verification-summary.json').write_text(json.dumps({'new_public_theorems':10,'retained_theorems':2,'with_permitted_axioms':12,'without_axioms':0,'full_definitions':13,'public_bytes':len(public),'public_sha256':digest(public),'aggregate_jobs':4007,'theorem_dependencies':78457,'committed_strict_sources':len(records)},indent=2)+'\n')
print(json.dumps({'strict_sources':len(records),'public_signatures':len(axioms),'full_definitions':13,'no_placeholders_or_heartbeat_changes':True,'old_Audit_exact_after_removing_new_imports':True}))
