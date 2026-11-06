from pathlib import Path
import hashlib,ast
p=Path('/tmp/mcfta-r88-hsk567-sparse-projector-author-20261106-1718/project_owned_rows.py')
s=p.lstat();I=lambda x:(x.st_dev,x.st_ino,x.st_size,x.st_mode,x.st_mtime_ns,x.st_ctime_ns)
assert s.st_size==4077 and p.resolve()==p
with p.open('rb',buffering=0) as f:
 assert I(__import__('os').fstat(f.fileno()))==I(s)
 b=f.read(4077)
 assert I(__import__('os').fstat(f.fileno()))==I(s)
assert I(p.lstat())==I(s) and hashlib.sha256(b).hexdigest()=='dda87191cfc6bf0c5b07fb47d0fd018b3e96c839784a7debe123f06200f16174'
a=ast.parse(b);n=next(n for n in a.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CONFIG' for t in n.targets));v=ast.literal_eval(n.value);cfg=list(v[0]);cfg[-1]=[(671,676)]
lines=b.splitlines(keepends=True);assert n.lineno==n.end_lineno
lines[n.lineno-1]=('CONFIG='+repr([tuple(cfg)])+'\n').encode();b=b''.join(lines)
for old,new,k in [(b'R86-SPARSE567',b'R86-MU573',3),(b'len(payloads)==8',b'len(payloads)==1',1),(b'len(copies)==8',b'len(copies)==1',1),(b'len(roles)-2+len(inputs_meta)',b'len(roles)-len(inputs)+len(inputs_meta)',1),(b"'Source_unique_delta':0",b"'Source_unique_delta':6",2),(b'selected owned rows only',b'selected six reserved rows only',1)]:
 assert b.count(old)==k
 b=b.replace(old,new)
exec(compile(b,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})
