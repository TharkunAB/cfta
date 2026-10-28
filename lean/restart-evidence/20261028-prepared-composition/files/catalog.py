from pathlib import Path
import json,re
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-prepared-composition-20261028')
modules=json.loads((a/'modules.json').read_text());new=[]
for m in modules:
 namespace=None
 for line in (r/'lean/MicroCFTA'/(m+'.lean')).read_text().splitlines():
  if line.startswith('namespace '): namespace=line.split()[1].removeprefix('MicroCFTA.')
  match=re.match(r'^theorem ([A-Za-z_][A-Za-z_0-9.]*)(?:\s|$)',line)
  if match:
   assert namespace,(m,line)
   new.append(namespace+'.'+match.group(1))
assert len(new)==len(set(new))
old=json.loads((a/'prior-public-declarations.json').read_text());assert not set(old)&set(new)
(a/'new-public-declarations.json').write_text(json.dumps(new,indent=2)+'\n')
(a/'public-declarations.json').write_text(json.dumps(old+new,indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),new_theorems=len(new),total=len(old)+len(new),new=new)))
