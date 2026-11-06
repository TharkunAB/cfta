from pathlib import Path
import hashlib,os
p=Path('/tmp/mcfta-r88-hsk584-literal-locator-author-20261106-1819/locate_matchmu_literal.py')
I=lambda s:(s.st_dev,s.st_ino,s.st_size,s.st_mode,s.st_mtime_ns,s.st_ctime_ns)
s=p.lstat();assert p.resolve()==p and s.st_size==3329
with p.open('rb',buffering=0) as f:
 assert I(os.fstat(f.fileno()))==I(s);b=f.read(3329);assert I(os.fstat(f.fileno()))==I(s)
assert I(p.lstat())==I(s) and hashlib.sha256(b).hexdigest()=='b415843d746d35ac195d01aa0253bde9f38c1c95bb9dca0567812d814bb5143c'
a=b"    result={'target_ASCII'"
z=b"    row_shapes=[]\n    for i in range(766,786):\n        line=raw[starts[i]:starts[i+1]-1];t=line.lstrip(bytes((32,9,13)));row_shapes.append({'row':i+1,'bytes_without_LF':len(line),'leading_ascii_ws_bytes':len(line)-len(t),'blank_ascii_ws':not t,'dashdash_space_prefix':t.startswith(b'-- ') or t==b'--','brace_dash_prefix':t.startswith(b'{-')})\n    result={'row_shapes_NOT_lexical_or_ignoredness':row_shapes,'target_ASCII'"
for old,new in [(a,z),(b'R87-MATCHMU584-LITERAL-LOCATORS',b'R87-MATCHMU591-ROW-SHAPES')]:
 assert b.count(old)==1;b=b.replace(old,new)
exec(compile(b,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})
