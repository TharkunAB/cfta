import hashlib,json,os,re,selectors,shlex,shutil,signal,stat,subprocess,sys,time
from pathlib import Path
NIX='/home/tritlo/.nix-profile/bin/nix-shell';SHELL='/home/tritlo/Code/mcfta/shell.nix';CWD='/home/tritlo/Code/mcfta'
OUT=Path(__file__).resolve().with_name('R85-536-PRIVATE-RUNTIME');ACTIVE=set();CAP=256*1024*1024
ids=lambda s:[s.st_dev,s.st_ino,s.st_size,stat.S_IMODE(s.st_mode),s.st_mtime_ns,s.st_ctime_ns]
def kill(p):
 try:os.killpg(p.pid,signal.SIGTERM)
 except ProcessLookupError:pass
 try:p.wait(timeout=.3)
 except subprocess.TimeoutExpired:pass
 try:os.killpg(p.pid,signal.SIGKILL)
 except ProcessLookupError:pass
 p.wait()
def interrupted(s,f):
 for p in list(ACTIVE):kill(p)
 raise RuntimeError('SIGNAL')
signal.signal(signal.SIGTERM,interrupted)
def run(argv,label):
 p=subprocess.Popen(argv,cwd=CWD,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True);ACTIVE.add(p)
 sel=selectors.DefaultSelector();buf=[bytearray(),bytearray()];limits=[4096,8192];reason=None;end=time.monotonic()+25
 for i,pipe in enumerate((p.stdout,p.stderr)):
  os.set_blocking(pipe.fileno(),False);sel.register(pipe,selectors.EVENT_READ,i)
 try:
  while sel.get_map():
   if time.monotonic()>end:reason='TIMEOUT';break
   for k,_ in sel.select(.1):
    i=k.data;b=os.read(k.fd,min(4096,limits[i]-len(buf[i])+1))
    if not b:sel.unregister(k.fileobj);continue
    if len(buf[i])+len(b)>limits[i]:reason='OUTPUT_CAP';buf[i].extend(b[:limits[i]-len(buf[i])]);break
    buf[i].extend(b)
   if reason:break
  if reason:kill(p)
  else:p.wait(timeout=max(.01,end-time.monotonic()))
 finally:
  if p.poll() is None:kill(p)
  ACTIVE.discard(p);sel.close();p.stdout.close();p.stderr.close()
 for suffix,b in zip(('stdout','stderr'),buf):
  with (OUT/(label+'.'+suffix+'.opaque')).open('xb') as f:f.write(b)
 return p.returncode,bytes(buf[0]),bytes(buf[1]),reason
def pin(path):
 q=os.path.realpath(path);s=os.lstat(q)
 if not stat.S_ISREG(s.st_mode) or s.st_size>CAP:raise ValueError('EXECUTABLE_CAP_REGULAR')
 h=hashlib.sha256();n=0;left=s.st_size
 with open(q,'rb',buffering=0) as f:
  if ids(os.fstat(f.fileno()))!=ids(s):raise ValueError('OPEN_IDENTITY')
  while left:
   b=f.read(min(65536,left))
   if not b:raise ValueError('SHORT_READ')
   left-=len(b);n+=len(b);h.update(b)
  if ids(os.fstat(f.fileno()))!=ids(s):raise ValueError('READ_IDENTITY')
 if ids(os.lstat(q))!=ids(s) or n!=s.st_size:raise ValueError('EXECUTABLE_DRIFT')
 return {'path':q,'bytes':n,'sha256':h.hexdigest(),'mode':oct(stat.S_IMODE(s.st_mode)),'identity':ids(s)}
def emit(d):
 b=(json.dumps(d,separators=(',',':'))+'\n').encode()
 if len(b)>4096:b=b'{"status":"STOP_OUTPUT_CAP","Source_query_delta":0}\n'
 sys.stdout.buffer.write(b);raise SystemExit(0 if d.get('status')=='PASS_NIX_METADATA_ONLY' and len(b)>80 else 1)
def inside():
 names=('cabal','ghc','ghc-pkg','hypha');paths={};pins={};results={};phases=[];stage='DISCOVERY';error=None
 try:
  for n in names:
   paths[n]=shutil.which(n)
   if paths[n] is None and n!='hypha':raise ValueError('REQUIRED_EXECUTABLE_MISSING')
   pins[n]=pin(paths[n]) if paths[n] else None
  stage='EXACT_VERSION_AND_PACKAGE_LABEL_QUERIES'
  jobs=[('cabal',[paths['cabal'],'--numeric-version'],None),('ghc',[paths['ghc'],'--numeric-version'],None),('Cabal',[paths['ghc-pkg'],'list','--simple-output','Cabal'],'Cabal'),('Cabal-syntax',[paths['ghc-pkg'],'list','--simple-output','Cabal-syntax'],'Cabal-syntax')]
  for label,argv,pkg in jobs:
   rc,out,err,stop=run(argv,label)
   if rc!=0 or stop:raise ValueError('QUERY_PROCESS_STOP')
   if pkg is None:
    if re.fullmatch(rb'[0-9]+(?:\.[0-9]+){1,4}\n?',out) is None:raise ValueError('NUMERIC_VERSION_SHAPE')
    value=out.rstrip(b'\n').decode('ascii')
   else:
    labels=out.split()
    if len(labels)>32 or any(re.fullmatch(re.escape(pkg.encode())+rb'-[0-9]+(?:\.[0-9]+){1,4}',x) is None for x in labels):raise ValueError('PACKAGE_LABEL_SHAPE')
    if any(b not in b' \t\r\n0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-.' for b in out):raise ValueError('PACKAGE_BYTES')
    value=[x.decode('ascii') for x in labels]
   results[label]={'value':value,'stderr_bytes':len(err),'stderr_sha256':hashlib.sha256(err).hexdigest()}
 except Exception as e:error=type(e).__name__
 for phase in ('DISTINCT_AFTER','SEPARATE_FINAL'):
  flags={}
  for n in paths:
   try:flags[n]=shutil.which(n)==paths[n] and (pin(paths[n]) if paths[n] else None)==pins.get(n)
   except Exception:flags[n]=False
  phases.append({'phase':phase,'logicalWhichAndPhysicalPin':flags})
 ok=error is None and len(paths)==4 and all(all(p['logicalWhichAndPhysicalPin'].values()) for p in phases)
 emit({'status':'PASS_NIX_METADATA_ONLY' if ok else 'STOP','metadata_only':True,'stage':stage,'exception_category':error,'logicalWhich':paths,'beforeCanonicalPhysicalPins':pins,'after_final':phases,'labels':results if ok else {},'hypha_invoked':False,'ABI_import_Source_correspondence':'UNKNOWN','Source_query_delta':0})
if sys.argv[1:]==['--inside']:inside()
if sys.argv[1:]:emit({'status':'STOP_ARGUMENTS','Source_query_delta':0})
try:
 OUT.mkdir(mode=0o700)
 rc,out,err,stop=run([NIX,SHELL,'--run',shlex.join([sys.executable,str(Path(__file__).resolve()),'--inside'])],'nix')
 if rc!=0 or stop:raise ValueError('NIX_PROCESS_STOP')
 d=json.loads(out)
 if not isinstance(d,dict) or d.get('metadata_only') is not True or d.get('status')!='PASS_NIX_METADATA_ONLY':raise ValueError('INSIDE_METADATA_STOP')
 emit(d)
except Exception as e:emit({'status':'STOP','metadata_only':True,'exception_category':type(e).__name__,'private_diagnostics':str(OUT),'Source_query_delta':0})
