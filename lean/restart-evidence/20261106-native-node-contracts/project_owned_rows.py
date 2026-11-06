import hashlib,json,os,runpy,sys
R='/tmp/mcfta-r87-hsk541-facade-receiver-author-20261106-1604/receive_facade.py'
D='/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/'
CONFIG=[('Type',922,36883,'f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77',[2096,207524,36883,33152,1793981792389035079,1793981792389035079],[(1,140),(141,280),(281,420),(608,611),(903,922)]),('Operations',887,38260,'1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836',[2096,207535,38260,33152,1793981792392322319,1793981792392322319],[(1,140),(141,280),(281,420)])]
with open(R,'rb') as f:b=f.read(5880)
assert len(b)==5879 and hashlib.sha256(b).hexdigest()=='5c57229b4c7d6248fe92a006bb2b8a60791ee4cf8d7f26257a449ee52a076c1c'
g=runpy.run_path(R);pin=g['pin'];sample=g['sampled'];phase=g['phase']
cb,cp=sample(pin(sys.argv[1]),32768);c=json.loads(cb)
b,bp=sample(c['basis'],4194304);book=json.loads(b)
assert 10750<=len(book['controls'])<=40000 and len(book['logical_controls'])>=8 and len(c['extras'])<=64
inputs=[{'path':D+'R85-OPAQUE-COPY564.'+name+'.PRIVATE.bin','bytes':n,'sha256':sha,'identity':i} for name,L,n,sha,i,cuts in CONFIG]
roles=[g['normalize'](x) for x in book['controls']]+[bp,cp,pin(R),pin(__file__)]+c['extras']+inputs
logical=book['logical_controls'];assert c['history'] in roles
ps=[];created=[];plans=[];copies=[];inputs_meta=[];errors=[]
try:
    ps.append(phase('BEFORE',roles,logical));assert ps[-1]['pass']
    payloads=[]
    for (name,L,n,sha,identity,cuts),e in zip(CONFIG,inputs):
        raw,current=sample(e,65536);assert current==e
        starts=[0]
        while True:
            q=raw.find(b'\n',starts[-1])
            if q<0:break
            starts.append(q+1)
        lf=len(starts)-1
        if starts[-1]!=len(raw):starts.append(len(raw))
        assert len(starts)-1==L
        inputs_meta.append({'Source':name,'input_role':len(roles)-2+len(inputs_meta),'physical_rows':L,'LF_count':lf,'terminal_LF':raw.endswith(b'\n')})
        for lo,hi in cuts:
            a,z=starts[lo-1],starts[hi];part=raw[a:z];assert 0<len(part)<=16384
            dst=D+'R86-SPARSE567.'+name+'.rows'+str(lo)+'-'+str(hi)+'.PRIVATE.bin'
            plans.append({'Source':name,'Original_rows_inclusive':[lo,hi],'Original_UTF8_bytes_halfopen':[a,z],'bytes':len(part),'LF_count':part.count(b'\n'),'terminal_LF':part.endswith(b'\n'),'path':dst})
            payloads.append((dst,part))
    assert len(payloads)==8 and all(not os.path.lexists(x) for x,_ in payloads)
    assert not os.path.lexists(D+'R86-SPARSE567.metadata.json')
    for dst,part in payloads:
        fd=os.open(dst,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600);created.append(dst)
        with os.fdopen(fd,'wb') as f:
            assert f.write(part)==len(part);f.flush();os.fsync(f.fileno())
        q=pin(dst);assert q['bytes']==len(part) and q['sha256']==hashlib.sha256(part).hexdigest();copies.append(q)
except Exception as exc:errors.append(type(exc).__name__)
for path in created:
    if any(x['path']==path for x in copies):continue
    try:copies.append(pin(path))
    except Exception as exc:errors.append(type(exc).__name__)
for name in ('DISTINCT_AFTER','SEPARATE_FINAL'):ps.append(phase(name,roles+copies,logical))
ok=not errors and len(copies)==8 and all(x['pass'] for x in ps)
out={'status':'SPARSE_BYTES_PROJECTED_ONLY' if ok else 'STOP','exception_kinds':errors,'basis':c['basis'],'new_expectations':roles[len(book['controls']):],'input_LF_metadata':inputs_meta,'cut_plans':plans,'created_cut_pins':copies,'phases':ps,'Source_unique_delta':0,'private_semantic_view_accepted':False,'Original_payload_read':False,'TYPE_API_runtime_accepted':False,'alias_pool':'Same ten Originals and two FINAL reservations; selected owned rows only'}
encoded=(json.dumps(out,separators=(',',':'))+'\n').encode();assert len(encoded)<=196608
with open(D+'R86-SPARSE567.metadata.json','xb') as f:f.write(encoded)
print(json.dumps({'status':out['status'],'private_cuts':len(copies),'Source_unique_delta':0,'private_semantic_view_accepted':False}))
raise SystemExit(0 if ok else 1)
