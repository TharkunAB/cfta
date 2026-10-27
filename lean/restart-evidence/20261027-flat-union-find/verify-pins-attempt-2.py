from pathlib import Path
import hashlib,json
root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-flat-union-find-20261027')
counts={'whole_files':0,'literal_spans':0}
def resolve(value):
 p=Path(value)
 return p if p.is_absolute() else root/p
def verify(data,node,label):
 assert len(data)==node['bytes'],(label,'bytes')
 assert hashlib.sha256(data).hexdigest()==node['sha256'],(label,'sha256')
 if 'lines' in node: assert len(data.splitlines())==node['lines'],(label,'lines')
def walk(node,context=None):
 if isinstance(node,list):
  for child in node: walk(child,context)
  return
 if not isinstance(node,dict): return
 source=node.get('source')
 if isinstance(source,str): context=resolve(source)
 elif isinstance(source,dict) and isinstance(source.get('path'),str): context=resolve(source['path'])
 if 'live' in node and isinstance(node['live'],dict): context=resolve(node['live']['path'])
 if isinstance(node.get('path'),str): context=resolve(node['path'])
 if isinstance(node.get('original'),str): context=resolve(node['original'])
 if context is None and isinstance(node.get('snapshot'),str): context=resolve(node['snapshot'])
 first=node.get('first',node.get('first_line'))
 last=node.get('last',node.get('last_line'))
 if first is not None and last is not None and 'sha256' in node:
  assert context is not None,node
  data=b''.join(context.read_bytes().splitlines(keepends=True)[first-1:last])
  verify(data,node,str(context)+':'+str(first)+'-'+str(last))
  for key in ['snapshot','path']:
   if isinstance(node.get(key),str): assert resolve(node[key]).read_bytes()==data
  counts['literal_spans']+=1
 elif 'sha256' in node and 'bytes' in node:
  paths=[]
  for key in ['path','snapshot','source']:
   if isinstance(node.get(key),str): paths.append(resolve(node[key]))
  for path in paths:
   verify(path.read_bytes(),node,str(path));counts['whole_files']+=1
 for child in node.values():
  if isinstance(child,(dict,list)): walk(child,context)
files=sorted(area.glob('*pins.json'))
for path in files: walk(json.loads(path.read_text()))
result=dict(counts,pin_files=len(files),status='pass',span_convention='Literal inclusive one-based source lines, retaining the final LF.')
(area/'pin-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
