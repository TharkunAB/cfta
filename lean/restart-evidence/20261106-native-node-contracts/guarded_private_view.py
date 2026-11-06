from pathlib import Path
import hashlib,os,stat,resource,sys
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
resource.setrlimit(resource.RLIMIT_FSIZE,(4194304,4194304))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
assert [(cg/n).read_text().strip() for n in ('memory.max','memory.high','memory.swap.max')]==['4294967296','4294967296','0']
p=Path('/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/R79-run-B418-capped-indexed-phase-actual-pools-compact-position-flags.py')
s=p.lstat();assert p.resolve()==p and stat.S_ISREG(s.st_mode) and s.st_size==6399
I=lambda x:(x.st_dev,x.st_ino,x.st_size,x.st_mode,x.st_mtime_ns,x.st_ctime_ns)
with p.open('rb',buffering=0) as f:
 assert I(os.fstat(f.fileno()))==I(s)
 b=f.read(6399)
 assert I(os.fstat(f.fileno()))==I(s)
assert len(b)==6399 and I(p.lstat())==I(s) and hashlib.sha256(b).hexdigest()=='1f460afaf9860da020b1da32d6d9f426b2b07f6bbbba7f44adf3f7a368fc2305'
old="def pin(path):\n    p = Path(path)\n    a = p.lstat()\n    assert p.resolve() == p and stat.S_ISREG(a.st_mode)\n    h = hashlib.sha256()\n    with p.open('rb') as f:\n        for b in iter(lambda: f.read(65536), b''):\n            h.update(b)\n    z = p.lstat()\n    ident = lambda s: [s.st_dev, s.st_ino, s.st_size, stat.S_IMODE(s.st_mode), s.st_mtime_ns, s.st_ctime_ns]\n    assert ident(a) == ident(z)\n    return {'path': str(p), 'bytes': a.st_size, 'sha256': h.hexdigest(), 'mode': oct(stat.S_IMODE(a.st_mode)), 'identity': ident(a)}\n\n"
new="def pin(path):\n    p = Path(path)\n    a = p.lstat()\n    assert p.resolve() == p and stat.S_ISREG(a.st_mode)\n    ident = lambda s: [s.st_dev, s.st_ino, s.st_size, stat.S_IMODE(s.st_mode), s.st_mtime_ns, s.st_ctime_ns]\n    h = hashlib.sha256()\n    left = a.st_size\n    with p.open('rb', buffering=0) as f:\n        assert ident(os.fstat(f.fileno())) == ident(a)\n        while left:\n            block = f.read(min(65536, left))\n            assert block\n            left -= len(block)\n            h.update(block)\n        assert ident(os.fstat(f.fileno())) == ident(a)\n    assert ident(a) == ident(p.lstat())\n    return {'path': str(p), 'bytes': a.st_size, 'sha256': h.hexdigest(), 'mode': oct(stat.S_IMODE(a.st_mode)), 'identity': ident(a)}\n\n"
assert b.count(old.encode())==1 and b.count(b"CAPS = {'stdout': 4096, 'stderr': 8192}")==1 and b.count(b'R79-B418-CAPPED')==2
b=b.replace(old.encode(),new.encode()).replace(b"CAPS = {'stdout': 4096, 'stderr': 8192}",b"CAPS = {'stdout': 16384, 'stderr': 8192}").replace(b'R79-B418-CAPPED',('R86-VIEW570-'+sys.argv[2]).encode()).replace(b'PROCESS_PASS_METADATA_ONLY',b'PROCESS_PASS_PRIVATE_SOURCE_VIEW')
assert len(sys.argv)==3 and sys.argv[2] in tuple(map(str,range(8)))
D='/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/R86-SPARSE567.'
C=['Type.rows1-140','Type.rows141-280','Type.rows281-420','Type.rows608-611','Type.rows903-922','Operations.rows1-140','Operations.rows141-280','Operations.rows281-420']
cut=D+C[int(sys.argv[2])]+'.PRIVATE.bin'
a=b"child = subprocess.Popen([sys.executable, job['helper'], *job['helper_args']],"
z=b"assert job['helper']=='/usr/bin/cat' and job['helper_args']==[ADMITTED_CUT]\n    child = subprocess.Popen([job['helper'], *job['helper_args']],"
assert b.count(a)==1
b=b.replace(a,z)
i=b.index(b"    print(json.dumps({'status': result['status']")
assert b[i:].endswith(b"'role_link': 'UNKNOWN'}))\n")
b=b[:i]+b"    if all_pass and result.get('exit')==0 and result['status']=='PROCESS_PASS_PRIVATE_SOURCE_VIEW':\n        es=[e for e in expected if e['path']==ADMITTED_CUT]\n        assert es and all(e==es[0] for e in es)\n        assert len(buffers['stdout'])==es[0]['bytes']<=16384 and hashlib.sha256(buffers['stdout']).hexdigest()==es[0]['sha256']\n        sys.stdout.buffer.write(buffers['stdout']);sys.stdout.buffer.flush()\n    else:\n        print(json.dumps({'status':result['status'],'all_fences_PASS':all_pass,'Source_view':False}))\n        raise SystemExit(1)\n"
exec(compile(b,str(p),'exec'),{'__name__':'__main__','__file__':str(p),'ADMITTED_CUT':cut})
