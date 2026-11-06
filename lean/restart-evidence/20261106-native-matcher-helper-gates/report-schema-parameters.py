from pathlib import Path
import hashlib,os
p=Path('/tmp/mcfta-r88-hsk577-report-reader-author-20261106-1804/read_report_metadata.py')
s=p.lstat();I=lambda x:(x.st_dev,x.st_ino,x.st_size,x.st_mode,x.st_mtime_ns,x.st_ctime_ns)
assert s.st_size==4245 and p.resolve()==p
with p.open('rb',buffering=0) as f:
 assert I(os.fstat(f.fileno()))==I(s)
 b=f.read(4245)
 assert I(os.fstat(f.fileno()))==I(s)
assert I(p.lstat())==I(s) and hashlib.sha256(b).hexdigest()=='ea39b618731bc96c34c6ab3921c319294fbecfe69b4eccd11de631a79c53b04d'
x=b"N={'name','identifier','decl_name'}"
y=x+b"\nW.update('target needle symbol module_name qualified_name file path source_file original rows_inclusive start_line end_line start_byte end_byte occurrences hits locations tokens declaration command commands catalogue index header full_command_span signature_spans equation_spans source_span top_level is_top_level scope'.split())"
a=b"if any((k in N and q=='matchMu') or k=='matchMu' for k,q in v.items())"
z=b"if any(q=='matchMu' or k=='matchMu' for k,q in v.items())"
u=b"'complete_defining_command_entry':None"
v=b"'module_object_schema':schema(root['module']) if isinstance(root,dict) and isinstance(root.get('module'),dict) else None,'target_catalogue_schemas':[schema(t) if isinstance(t,dict) else {'shape':shape(t)} for t in root.get('targets',[])[:16]] if isinstance(root,dict) and isinstance(root.get('targets'),list) else None,'complete_defining_command_entry':None"
for old,new in [(x,y),(a,z),(u,v),(b'R86-MATCHMU577',b'R87-MATCHMU582')]:
 assert b.count(old)==1;b=b.replace(old,new)
exec(compile(b,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})
