import hashlib,json,runpy,sys
R='/tmp/mcfta-r87-hsk541-facade-receiver-author-20261106-1604/receive_facade.py'
P='/tmp/mcfta-haskell-type-locator-review-supplement-20261104/TYPE-LEXICAL-LOCATOR-RESULT-v1.json'
OUT='/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/R86-MATCHMU577.metadata.json'
W=set('module source_module kind decl_kind name identifier decl_name span full_span signature_span equation_span equations signature enclosure complete module_level declarations bindings targets source pins syntax errors missing status start end rows'.split())
N={'name','identifier','decl_name'}
with open(R,'rb') as f:b=f.read(5880)
assert len(b)==5879 and hashlib.sha256(b).hexdigest()=='5c57229b4c7d6248fe92a006bb2b8a60791ee4cf8d7f26257a449ee52a076c1c'
g=runpy.run_path(R);pin=g['pin'];sample=g['sampled'];phase=g['phase']
cb,cp=sample(pin(sys.argv[1]),32768);c=json.loads(cb)
b,bp=sample(c['basis'],4194304);book=json.loads(b)
assert 10820<=len(book['controls'])<=40000 and len(book['logical_controls'])>=9 and len(c['extras'])<=64
roles=[g['normalize'](x) for x in book['controls']]+[bp,cp,pin(R),pin(__file__)]+c['extras']
logical=book['logical_controls'];e=c['report']
assert c['history'] in roles and e in roles and e['path']==P and e['bytes']==33526 and e['sha256']=='e51693eaf3dcc0117aef8bd27ba67290ae7a0f81b3c4dcf2eff4baceff229556'
ps=[];error=None;data=None

def pairs(items):
    d={}
    for k,v in items:
        assert k not in d;d[k]=v
    return d

def shape(v):
    if isinstance(v,dict):return ['OBJECT',len(v)]
    if isinstance(v,list):return ['ARRAY',len(v)]
    if isinstance(v,str):return ['STRING_UTF8_BYTES',len(v.encode('utf8'))]
    return ['NULL' if v is None else 'BOOLEAN' if isinstance(v,bool) else 'NUMBER']

def schema(d):
    assert len(d)<=256
    return {'known_fields':{k:shape(v) for k,v in d.items() if k in W},'other_key_count':sum(k not in W for k in d)}
try:
    ps.append(phase('BEFORE',roles,logical));assert ps[-1]['pass']
    raw,current=sample(e,33526);assert current==e
    depth=0;quoted=False;escape=False
    for ch in raw:
        if quoted:
            if escape:escape=False
            elif ch==92:escape=True
            elif ch==34:quoted=False
        elif ch==34:quoted=True
        elif ch in (123,91):depth+=1;assert depth<=24
        elif ch in (125,93):depth-=1;assert depth>=0
    assert not quoted and depth==0
    def reject(x):raise ValueError()
    root=json.loads(raw.decode('utf8','strict'),object_pairs_hook=pairs,parse_constant=reject)
    stack=[(root,[])];nodes=0;matches=[]
    while stack:
        v,address=stack.pop();nodes+=1;assert nodes<=8192 and len(address)<=24
        if isinstance(v,dict):
            assert len(v)<=256
            if any((k in N and q=='matchMu') or k=='matchMu' for k,q in v.items()):matches.append((address,v))
            for i,q in enumerate(v.values()):stack.append((q,address+[i]))
        elif isinstance(v,list):
            assert len(v)<=4096
            for i,q in enumerate(v):stack.append((q,address+[i]))
    data={'target':'matchMu','root_kind':shape(root),'root_whitelist_schema':schema(root) if isinstance(root,dict) else None,'nodes':nodes,'literal_name_or_key_record_count':len(matches),'single_target_record_schema':schema(matches[0][1]) if len(matches)==1 else None,'single_target_record_numeric_address':matches[0][0] if len(matches)==1 else None,'complete_defining_command_entry':None,'result':'UNKNOWN_SCHEMA_UNBOUND; name matches do not certify declaration, owner or extent'}
except Exception as exc:error=type(exc).__name__
for name in ('DISTINCT_AFTER','SEPARATE_FINAL'):ps.append(phase(name,roles,logical))
ok=not error and all(x['pass'] for x in ps)
out={'status':'METADATA_ONLY_UNKNOWN' if ok else 'STOP','exception_kind':error,'basis':c['basis'],'new_expectations':roles[len(book['controls']):],'phases':ps,'selected_metadata':data if ok else None,'Source_API_accepted':False,'Source_unique_delta':0,'complete_command_accepted':False}
encoded=(json.dumps(out,separators=(',',':'))+'\n').encode();assert len(encoded)<=196608
with open(OUT,'xb') as f:f.write(encoded)
print(json.dumps({'status':out['status'],'Source_API_accepted':False,'complete_command_accepted':False}))
raise SystemExit(0 if ok else 1)
