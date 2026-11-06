import hashlib,json,os,runpy,sys
R='/tmp/mcfta-r87-hsk541-facade-receiver-author-20261106-1604/receive_facade.py'
ROOT='/tmp/mcfta-haskell-activation-carrier-20261104/'
ROOTS=[ROOT+'source-inputs-stage1',ROOT+'source-inputs-stage2']
TARGETS={'Type.hs':(36883,'f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77'),'Operations.hs':(38260,'1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836')}
with open(R,'rb') as f:b=f.read(5880)
assert len(b)==5879 and hashlib.sha256(b).hexdigest()=='5c57229b4c7d6248fe92a006bb2b8a60791ee4cf8d7f26257a449ee52a076c1c'
g=runpy.run_path(R);pin=g['pin'];sample=g['sampled'];phase=g['phase'];identity=g['identity']
cb,cp=sample(pin(sys.argv[1]),32768);c=json.loads(cb)
b,bp=sample(c['basis'],4194304);book=json.loads(b)
assert 10716<=len(book['controls'])<=40000 and len(book['logical_controls'])>=8
assert len(c['extras'])<=64
roles=[g['normalize'](x) for x in book['controls']]+[bp,cp,pin(R),pin(__file__)]+c['extras']
assert c['history'] in roles
assert any(x['sha256']=='7597fef16f58067d31fb31fcad17eca4bfecd85549baea96f3d4db2d25fdcd36' and x['bytes']==3332157 for x in roles)
logical=book['logical_controls'];ps=[];ds=[];found=[];error=None;counts=[0,0]
prefix=c['output_prefix'];assert prefix=='/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/R85-TYPE-OPS-CACHE560'
def directory(path):
    assert os.path.realpath(path)==path and len(path.encode())<=512
    st=os.lstat(path);assert g['stat'].S_ISDIR(st.st_mode)
    return {'path':path,'identity':identity(st)}
def inventory(root):
    stack=[(root,0)];seen=set()
    while stack:
        path,depth=stack.pop();assert depth<=8;d=directory(path)
        key=tuple(d['identity'][:2]);assert key not in seen;seen.add(key)
        counts[0]+=1;assert counts[0]<=64
        ds.append(d)
        with os.scandir(path) as entries:
            for e in entries:
                counts[1]+=1;assert counts[1]<=1024
                assert not e.is_symlink()
                q=e.path;assert len(q.encode())<=512 and os.path.realpath(q)==q
                if e.is_dir(follow_symlinks=False):stack.append((q,depth+1))
                elif any(q.endswith('/Data/CFTA/Interned/'+name) for name in TARGETS):
                    assert len(found)<4
                    st=os.lstat(q);assert g['stat'].S_ISREG(st.st_mode) and st.st_size<=65536
                    before=identity(st);item=pin(q);assert item['identity']==before
                    expected=TARGETS[e.name]
                    found.append({'root':ROOTS.index(root),'relative':os.path.relpath(q,root),'pin':item,'positive_byte_alias':(item['bytes'],item['sha256'])==expected})
        assert directory(path)==d
try:
    ps.append(phase('BEFORE',roles,logical));assert ps[-1]['pass']
    for root in ROOTS:
        try:inventory(root)
        except FileNotFoundError:
            if not os.path.lexists(root):
                ds.append({'path':root,'missing':True})
            else:raise
except Exception as e:error=type(e).__name__
def directory_phase():
    flags=[]
    for d in ds:
        try:flags.append(not os.path.lexists(d['path']) if d.get('missing') else directory(d['path'])==d)
        except Exception:flags.append(False)
    return flags
for name in ('DISTINCT_AFTER','SEPARATE_FINAL'):
    ps.append(phase(name,roles+[x['pin'] for x in found],logical));ps[-1]['directory_flags']=directory_phase()
ok=not error and all(x['pass'] and all(x.get('directory_flags',[])) for x in ps)
out={'status':'METADATA_INVENTORY_PASS' if ok else 'STOP','exception_kind':error,'basis':c['basis'],'current_new_roles':roles[len(book['controls']):],'phases':ps,'directory_expectations':ds,'directory_entry_counts':counts,'candidates':found,'positive_aliases':sum(x['positive_byte_alias'] for x in found),'Source_unique_delta':0,'Source_API_accepted':False,'owner_runtime_meaning':'UNKNOWN; only stable byte aliases'}
encoded=(json.dumps(out,separators=(',',':'))+'\n').encode();assert len(encoded)<=196608
with open(prefix+'.metadata.json','xb') as f:f.write(encoded)
print(json.dumps({'status':out['status'],'candidates':len(found),'positive_aliases':out['positive_aliases'],'Source_API_accepted':False}))
raise SystemExit(0 if ok else 1)
