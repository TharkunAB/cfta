import hashlib,json,os,stat,sys
from pathlib import Path
MP='/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/R83-PREFLIGHT492/EXPR-491B-PREFLIGHT-OUTPUT/metadata.json'
MH='2174afcea03c0f980698265f3f2889b2b3b1a6d80ee8b9f9a362629ee67eace0'
TRACE='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/lib/lean/Lean/Expr.trace'
RAW=[289,0,513,13,297,10,297,14]
def ident(s):return[s.st_dev,s.st_ino,s.st_size,stat.S_IMODE(s.st_mode),s.st_mtime_ns,s.st_ctime_ns]
def sample(p,cap):
 s=os.lstat(p)
 if not stat.S_ISREG(s.st_mode) or os.path.realpath(p)!=str(p) or s.st_size>cap:raise ValueError('PHYSICAL')
 a=ident(s);remaining=s.st_size;h=hashlib.sha256()
 with open(p,'rb',buffering=0) as f:
  while remaining:
   b=f.read(min(65536,remaining))
   if not b:raise ValueError('SHORT')
   remaining-=len(b);h.update(b)
 if ident(os.lstat(p))!=a:raise ValueError('DRIFT')
 return{'path':str(p),'bytes':a[2],'sha256':h.hexdigest(),'mode':oct(a[3]),'identity':a}
def absent():
 try:os.lstat(TRACE);return False
 except FileNotFoundError:return True
out=Path(sys.argv[1]);cut=out/'PRIVATE-Expr-Source-Prefix1-514.opaque';E=[];cp=None;created=False;error=None;stage='CONTROL';rows={};widths=[];flags=[];ph=[]
try:
 with open(MP,'rb',buffering=0) as f:b=f.read(1928)
 if len(b)!=1928 or hashlib.sha256(b).hexdigest()!=MH:raise ValueError('CONTROL')
 E=json.loads(b)['actual_physicalfive'][:5]
 if len(E)!=5 or len(sys.argv)!=2 or not out.is_dir() or any(out.iterdir()):raise ValueError('CONTEXT')
 stage='FIVE_INPUT_BEFORE_TRACE_ABSENCE'
 for e in E:
  if sample(e['path'],e['bytes'])!=e:raise ValueError('INPUT_PIN')
 if not absent():raise ValueError('TRACE_CHANGED')
 source=E[0]
 if source['bytes']!=87215 or source['sha256']!='b9a91d9d170201c2a3622b9c55d694466f54e0e1b8f6068a2d296ff98650169c':raise ValueError('SOURCE_IDENTITY')
 stage='EXACT_UNBUFFERED_PREFIX_514';total=0;row=1;line=bytearray()
 with open(source['path'],'rb',buffering=0) as src,cut.open('xb') as dst:
  created=True
  while row<=514:
   if total>=87215:raise ValueError('PREFIX_BYTE_CAP')
   b=src.read(1)
   if not b:raise ValueError('PREFIX_SHORT')
   if dst.write(b)!=1:raise ValueError('SHORT_WRITE')
   total+=1;line.extend(b)
   if b==b'\n':
    if row in (290,298,514):rows[row]=bytes(line)
    line.clear();row+=1
 if row!=515 or line:raise ValueError('PREFIX_ROWS')
 cp=sample(cut,87215)
 if cp['bytes']!=total or cp['identity'][:2]==source['identity'][:2]:raise ValueError('CUT_IDENTITY')
 stage='FOUR_LOCAL_UTF16_BOUNDARIES'
 text={}
 for r in (290,298,514):
  b=rows[r]
  if not b.endswith(b'\n') or b.endswith(b'\r\n'):raise ValueError('ENDING')
  text[r]=b[:-1].decode('utf-8').encode('utf-16-le');widths.append(len(text[r])//2)
 def boundary(r,c):
  u=text[r]
  if c*2>len(u):return False
  try:u[:c*2].decode('utf-16-le');u[c*2:].decode('utf-16-le');return True
  except UnicodeError:return False
 fs,fe,ns,ne=[tuple(RAW[i:i+2]) for i in range(0,8,2)]
 flags=[boundary(290,0),boundary(514,13),boundary(298,10),boundary(298,14),fs<=ns<ne<=fe,text[298][20:28].decode('utf-16-le')=='Expr',row==515 and len(rows)==3]
 if not all(flags):raise ValueError('LOCAL_ENDPOINT')
except Exception as e:error=type(e).__name__
for phase in ('DISTINCT_AFTER','SEPARATE_FINAL'):
 f=[]
 for e in E:
  try:f.append(sample(e['path'],e['bytes'])==e)
  except Exception:f.append(False)
 try:a=absent()
 except Exception:a=False
 try:
  if created:
   c=sample(cut,87215)
   if cp is None:cp=c
   stable=c==cp
  else:stable=True
 except Exception:stable=False
 ph.append({'phase':phase,'five_input_flags':f,'trace_absent':a,'private_cut_stable':stable})
ok=error is None and len(flags)==7 and all(flags) and all(len(x['five_input_flags'])==5 and all(x['five_input_flags']) and x['trace_absent'] and x['private_cut_stable'] for x in ph)
r={'status':'PASS_CAPTURE_AND_LOCAL_COORDINATES_ONLY' if ok else 'STOP','stage':stage,'exception_category':error,'private_cut_pin':cp,'raw8':RAW,'prefix_rows':[1,514],'selected_width_rows':[290,298,514],'three_UTF16_widths':widths,'seven_flags':flags,'phases':ph,'partial_cut_retained':created and not ok,'private_family_receipt':'NOT_AUTHORIZED_BY_CAPTURE','Source_context_SourceObject_loadedfile':'NOT_ESTABLISHED'}
b=(json.dumps(r,separators=(',',':'))+'\n').encode()
if len(b)>8192:raise SystemExit(2)
with(out/'capture-metadata.json').open('xb') as f:f.write(b)
s={'status':r['status'],'metadata_bytes':len(b),'metadata_sha256':hashlib.sha256(b).hexdigest(),'private_Source_text_output':False}
b=(json.dumps(s,separators=(',',':'))+'\n').encode()
if len(b)>2048:raise SystemExit(2)
sys.stdout.buffer.write(b)
raise SystemExit(0 if ok else 1)
