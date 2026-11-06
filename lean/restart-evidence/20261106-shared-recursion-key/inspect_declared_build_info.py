import hashlib,json,os,stat,sys
P='/home/tritlo/Code/mcfta/dist-newstyle/build/x86_64-linux/ghc-9.14.1/cfta-0.1.0.0/noopt/build-info.json'
I=lambda s:[s.st_dev,s.st_ino,s.st_size,stat.S_IMODE(s.st_mode),s.st_mtime_ns,s.st_ctime_ns]
def sample():
 try:s=os.lstat(P)
 except FileNotFoundError:return None,None
 if os.path.realpath(P)!=P or not stat.S_ISREG(s.st_mode) or s.st_size>1048576:raise ValueError('FILE_KIND_SIZE')
 i=I(s)
 with open(P,'rb',buffering=0) as f:
  if I(os.fstat(f.fileno()))!=i:raise ValueError('OPEN_IDENTITY')
  b=f.read(s.st_size)
  if len(b)!=s.st_size or I(os.fstat(f.fileno()))!=i:raise ValueError('READ_IDENTITY')
 if I(os.lstat(P))!=i:raise ValueError('PATH_IDENTITY')
 return {'path':P,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'mode':oct(i[3]),'identity':i},b
def unique(pairs):
 d={}
 for k,v in pairs:
  if k in d:raise ValueError('DUPLICATE_KEY')
  d[k]=v
 return d
def no_constant(x):raise ValueError('NONFINITE')
def labels(x,keys):
 if not isinstance(x,dict):raise ValueError('DICT')
 out={}
 for k in keys:
  if k in x:
   v=x[k]
   if not isinstance(v,str) or len(v.encode())>1024 or any(ord(c)<32 for c in v):raise ValueError('LABEL')
   out[k]=v
 return out
r={'status':'STOP','Source_workflow_query_delta':0};pin=None;flags=[]
try:
 pin,b=sample();flags.append(True)
 if pin is None:r['status']='MISSING_DECLARED_BUILD_INFO'
 else:
  j=json.loads(b,object_pairs_hook=unique,parse_constant=no_constant)
  if not isinstance(j,dict) or len(j)>64:raise ValueError('ROOT')
  r['root_keys']=list(j)
  r['compiler']=labels(j.get('compiler',{}),('path','id','flavour'))
  components=j.get('components',[])
  if not isinstance(components,list) or len(components)>256:raise ValueError('COMPONENTS')
  r['components']=[]
  for c in components:
   if not isinstance(c,dict) or len(c)>64:raise ValueError('COMPONENT')
   v=labels(c,('unit-id','component-name','type','name'));v['keys']=list(c)
   for k in ('compiler-args','modules','src-files','hs-src-dirs'):
    if k in c:
     if not isinstance(c[k],list) or len(c[k])>8192:raise ValueError('LIST')
     v[k+'_count']=len(c[k])
   r['components'].append(v)
  r['status']='PRESENT_METADATA_SCHEMA_ONLY'
except Exception as e:r['status']='STOP';r['exception_kind']=type(e).__name__
for phase in ('DISTINCT_AFTER','SEPARATE_FINAL'):
 try:q,_=sample();flags.append(q==pin)
 except Exception:flags.append(False)
r['pin']=pin;r['before_after_final']=flags
if flags!=[True,True,True]:r['status']='STOP'
b=(json.dumps(r,separators=(',',':'))+'\n').encode()
if len(b)>4096:b=b'{"status":"STOP_OUTPUT_CAP"}\n'
sys.stdout.buffer.write(b)
raise SystemExit(0 if r['status'] in ('MISSING_DECLARED_BUILD_INFO','PRESENT_METADATA_SCHEMA_ONLY') else 1)
