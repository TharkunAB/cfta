import hashlib,json,os,runpy,sys
R='/tmp/mcfta-r87-hsk541-facade-receiver-author-20261106-1604/receive_facade.py'
BASE='/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/'
OUT='/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/R85-OPAQUE-COPY564'
SOURCES=[('Type',36883,'f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77'),('Operations',38260,'1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836')]
with open(R,'rb') as f:b=f.read(5880)
assert len(b)==5879 and hashlib.sha256(b).hexdigest()=='5c57229b4c7d6248fe92a006bb2b8a60791ee4cf8d7f26257a449ee52a076c1c'
g=runpy.run_path(R);pin=g['pin'];sample=g['sampled'];phase=g['phase'];identity=g['identity']
cb,cp=sample(pin(sys.argv[1]),32768);c=json.loads(cb)
b,bp=sample(c['basis'],4194304);book=json.loads(b)
assert 10731<=len(book['controls'])<=40000 and len(book['logical_controls'])>=8 and len(c['extras'])<=64
roles=[g['normalize'](x) for x in book['controls']]+[bp,cp,pin(R),pin(__file__)]+c['extras']
logical=book['logical_controls'];assert c['history'] in roles
selected=[]
for name,n,sha in SOURCES:
    indices=[i for i,x in enumerate(roles) if x['path']==BASE+name+'.hs']
    assert indices
    e=roles[indices[0]];assert e['bytes']==n and e['sha256']==sha
    assert all(roles[i]==e for i in indices)
    selected.append((name,e,indices))
ps=[];copies=[];errors=[];created=[]
def copy_one(name,e):
    src=e['path'];dst=OUT+'.'+name+'.PRIVATE.bin'
    assert os.path.realpath(src)==src and os.path.realpath(os.path.dirname(dst))==os.path.dirname(dst)
    a=os.open(src,os.O_RDONLY|os.O_NOFOLLOW)
    try:
        assert identity(os.fstat(a))==e['identity']==identity(os.lstat(src))
        z=os.open(dst,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600);created.append((name,dst))
        try:
            assert (os.fstat(z).st_dev,os.fstat(z).st_ino)!=tuple(e['identity'][:2])
            remaining=e['bytes'];digest=hashlib.sha256()
            while remaining:
                block=os.read(a,min(131072,remaining));assert block
                remaining-=len(block);digest.update(block);view=memoryview(block)
                while view:
                    written=os.write(z,view);assert written>0;view=view[written:]
            os.fsync(z)
            assert os.fstat(z).st_size==e['bytes'] and digest.hexdigest()==e['sha256']
            assert identity(os.fstat(a))==e['identity']==identity(os.lstat(src))
            expected=identity(os.fstat(z))
        finally:os.close(z)
    finally:os.close(a)
    q=pin(dst);assert q['identity']==expected and (q['bytes'],q['sha256'])==(e['bytes'],e['sha256'])
try:
    ps.append(phase('BEFORE',roles,logical));assert ps[-1]['pass']
    assert all(not os.path.lexists(OUT+'.'+name+'.PRIVATE.bin') for name,_,_ in SOURCES)
    assert not os.path.lexists(OUT+'.metadata.json')
    for name,e,_ in selected:copy_one(name,e)
except Exception as exc:errors.append(type(exc).__name__)
for name,dst in created:
    try:
        q=pin(dst);e=next(x for tag,x,_ in selected if tag==name)
        copies.append({'Source':name,'pin':q,'positive_byte_alias':(q['bytes'],q['sha256'])==(e['bytes'],e['sha256']) and q['identity'][:2]!=e['identity'][:2]})
    except Exception as exc:errors.append(type(exc).__name__)
for tag in ('DISTINCT_AFTER','SEPARATE_FINAL'):
    ps.append(phase(tag,roles+[x['pin'] for x in copies],logical))
ok=not errors and len(copies)==2 and all(x['positive_byte_alias'] for x in copies) and all(x['pass'] for x in ps)
out={'status':'OPAQUE_COPY_PASS_ONLY' if ok else 'STOP','exception_kinds':errors,'basis':c['basis'],'new_control_expectations':roles[len(book['controls']):],'Source_role_indices':{name:indices for name,_,indices in selected},'created_paths':created,'copies':copies,'phases':ps,'Source_unique_delta':0,'Source_view_accepted':False,'ownership_promotion':False,'provider_runtime_meaning':'UNKNOWN; same Original byte-alias pools only'}
encoded=(json.dumps(out,separators=(',',':'))+'\n').encode();assert len(encoded)<=196608
with open(OUT+'.metadata.json','xb') as f:f.write(encoded)
print(json.dumps({'status':out['status'],'private_copies':len(copies),'Source_view_accepted':False}))
raise SystemExit(0 if ok else 1)
