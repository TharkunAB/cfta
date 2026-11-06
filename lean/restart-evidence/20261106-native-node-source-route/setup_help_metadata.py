import hashlib,json,os,re,selectors,shlex,shutil,signal,stat,subprocess,sys,time
from pathlib import Path
NIX='/home/tritlo/.nix-profile/bin/nix-shell';SHELL='/home/tritlo/Code/mcfta/shell.nix';CWD='/home/tritlo/Code/mcfta'
A='/home/tritlo/.ghcup/bin/cabal';CAN='/home/tritlo/.ghcup/cabal/3.18.1.0/cabal';SHA='19387589519124132b37a2d541c8a7ce9540669e8bdc1c382243b098fac0129f'
OUT=Path(__file__).resolve().with_name('R85-550-PRIVATE-HELP');ACTIVE=set()
WORDS=('act-as-setup','show-build-info','build-info','build','repl','--build-type','--ghc-version','--builddir','--with-ghc','--with-repl','--repl-no-load','--dry-run','--enable-build-info')
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
def run(argv,label,limit):
 p=subprocess.Popen(argv,cwd=CWD,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True);ACTIVE.add(p)
 sel=selectors.DefaultSelector();buf=[bytearray(),bytearray()];caps=[limit,8192];why=None;end=time.monotonic()+25
 for i,pipe in enumerate((p.stdout,p.stderr)):
  os.set_blocking(pipe.fileno(),False);sel.register(pipe,selectors.EVENT_READ,i)
 try:
  while sel.get_map():
   if time.monotonic()>end:why='TIMEOUT';break
   for k,_ in sel.select(.1):
    i=k.data;b=os.read(k.fd,min(4096,caps[i]-len(buf[i])+1))
    if not b:sel.unregister(k.fileobj);continue
    if len(buf[i])+len(b)>caps[i]:why='OUTPUT_CAP';buf[i].extend(b[:caps[i]-len(buf[i])]);break
    buf[i].extend(b)
   if why:break
  if why:kill(p)
  else:p.wait(timeout=max(.01,end-time.monotonic()))
 finally:
  if p.poll() is None:kill(p)
  ACTIVE.discard(p);sel.close();p.stdout.close();p.stderr.close()
 for suffix,b in zip(('stdout','stderr'),buf):
  with (OUT/(label+'.'+suffix+'.opaque')).open('xb') as f:f.write(b)
 return p.returncode,bytes(buf[0]),why
def executable():
 if shutil.which('cabal')!=A or os.path.realpath(A)!=CAN:raise ValueError('SELECTED_ALIAS')
 s=os.lstat(CAN)
 if not stat.S_ISREG(s.st_mode) or s.st_size!=39881384 or s.st_size>256*1024*1024:raise ValueError('SAMPLED_SIZE')
 h=hashlib.sha256();left=s.st_size
 with open(CAN,'rb',buffering=0) as f:
  while left:
   b=f.read(min(65536,left))
   if not b:raise ValueError('SHORT_EXECUTABLE')
   left-=len(b);h.update(b)
 if ids(os.lstat(CAN))!=ids(s) or h.hexdigest()!=SHA:raise ValueError('EXECUTABLE_PIN')
 a=os.lstat(A)
 return {'physical':{'path':CAN,'bytes':s.st_size,'sha256':SHA,'mode':oct(stat.S_IMODE(s.st_mode)),'identity':ids(s)},'logical':{'which':A,'alias_identity':ids(a),'full_st_mode':a.st_mode,'symlink':stat.S_ISLNK(a.st_mode),'link_target':os.readlink(A) if stat.S_ISLNK(a.st_mode) else None}}
def project(b):
 usage=[]
 for line in b.split(b'\n'):
  line=line.lstrip(b' \t')
  if not line.startswith(b'Usage:'):continue
  if any(c<32 or c>126 for c in line):raise ValueError('USAGE_ASCII')
  usage.append(line.decode('ascii'))
 if len(usage)>4 or sum(len(x) for x in usage)>512:raise ValueError('USAGE_CAP')
 hits={w:re.search(rb'(?<![A-Za-z0-9_-])'+re.escape(w.encode())+rb'(?![A-Za-z0-9_-])',b) is not None for w in WORDS}
 versions={n:[x.decode('ascii') for x in re.findall(p,b)] for n,p in (
  ('executable',rb'(?m)^cabal-install version ([0-9.]+)\r?$'),
  ('linked_Cabal',rb'(?m)^compiled using version ([0-9.]+) of the Cabal library\r?$'))}
 if any(len(v)>2 or any(len(x)>32 for x in v) for v in versions.values()):raise ValueError('VERSION_CAP')
 return {'Usage':usage,'literal_whitelist_occurrences':hits,'version_labels':versions}
def emit(d):
 b=(json.dumps(d,separators=(',',':'))+'\n').encode()
 if len(b)>4096:d={'status':'STOP_PUBLIC_CAP','metadata_only':True};b=(json.dumps(d)+'\n').encode()
 sys.stdout.buffer.write(b);raise SystemExit(0 if d.get('status')=='PASS_STATIC_HELP_METADATA_ONLY' else 1)
def inside():
 expected=None;error=None;rows=[];phases=[]
 try:
  expected=executable()
  for label,args in [('cabal-version',['--version']),('simple-setup-help',['act-as-setup','--build-type=Simple','--','--help'])]:
   rc,b,why=run([A]+args,label,32768)
   if why:raise ValueError('HELP_PROCESS_BOUND')
   rows.append({'command':label,'exitcode':rc,**project(b)})
 except Exception as e:error=type(e).__name__
 for phase in ('DISTINCT_AFTER','SEPARATE_FINAL'):
  try:ok=expected is not None and executable()==expected
  except Exception:ok=False
  phases.append({'phase':phase,'physical_logical_match':ok})
 ok=error is None and len(rows)==2 and all(p['physical_logical_match'] for p in phases)
 emit({'status':'PASS_STATIC_HELP_METADATA_ONLY' if ok else 'STOP','metadata_only':True,'exception_category':error,'before_executable':expected,'after_final':phases,'help':rows if ok else [],'command_semantics_ABI':'NOT_ESTABLISHED','Source_query_delta':0})
if sys.argv[1:]==['--inside']:inside()
if sys.argv[1:]:emit({'status':'STOP_ARGUMENTS','metadata_only':True})
try:
 OUT.mkdir(mode=0o700)
 rc,b,why=run([NIX,SHELL,'--run',shlex.join([sys.executable,str(Path(__file__).resolve()),'--inside'])],'nix',4096)
 if rc or why:raise ValueError('NIX_PROCESS_STOP')
 d=json.loads(b)
 if not isinstance(d,dict) or d.get('metadata_only') is not True or d.get('status')!='PASS_STATIC_HELP_METADATA_ONLY':raise ValueError('INNER_METADATA_STOP')
 emit(d)
except Exception as e:emit({'status':'STOP','metadata_only':True,'exception_category':type(e).__name__,'private_diagnostics':str(OUT),'Source_query_delta':0})
