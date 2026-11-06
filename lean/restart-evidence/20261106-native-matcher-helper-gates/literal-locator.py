import bisect,hashlib,json,runpy,sys
R='/tmp/mcfta-r87-hsk541-facade-receiver-author-20261106-1604/receive_facade.py'
D='/tmp/mcfta-runtime-packet-producer-normal-20261104-1205/'
E={'path':D+'R85-OPAQUE-COPY564.Type.PRIVATE.bin','bytes':36883,'sha256':'f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77','identity':[2096,207524,36883,33152,1793981792389035079,1793981792389035079]}
with open(R,'rb') as f:b=f.read(5880)
assert len(b)==5879 and hashlib.sha256(b).hexdigest()=='5c57229b4c7d6248fe92a006bb2b8a60791ee4cf8d7f26257a449ee52a076c1c'
g=runpy.run_path(R);pin=g['pin'];sample=g['sampled'];phase=g['phase']
cb,cp=sample(pin(sys.argv[1]),32768);c=json.loads(cb)
b,bp=sample(c['basis'],4194304);book=json.loads(b)
assert 10850<=len(book['controls'])<=40000 and len(book['logical_controls'])>=9 and len(c['extras'])<=64
roles=[g['normalize'](x) for x in book['controls']]+[bp,cp,pin(R),pin(__file__)]+c['extras']
logical=book['logical_controls'];assert c['history'] in roles and E in roles
ps=[];error=None;result=None
try:
    ps.append(phase('BEFORE',roles,logical));assert ps[-1]['pass']
    raw,current=sample(E,36883);assert current==E
    starts=[0]
    while True:
        q=raw.find(b'\n',starts[-1])
        if q<0:break
        starts.append(q+1)
    assert raw.endswith(b'\n') and len(starts)-1==922
    word=set(b'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_\x27')
    hits=[];scan=0;literal_count=0;target=b'matchMu'
    while True:
        a=raw.find(target,scan)
        if a<0:break
        z=a+len(target);scan=z;literal_count+=1;assert literal_count<=16
        if (a and raw[a-1] in word) or (z<len(raw) and raw[z] in word):continue
        row=bisect.bisect_right(starts,a)-1;column=a-starts[row]+1
        boundary=None
        for j in range(row+1,922):
            if starts[j]<starts[j+1] and raw[starts[j]] not in (9,10,13,32):
                boundary={'row':j+1,'byte_offset':starts[j]};break
        hits.append({'row':row+1,'byte_column_one_based':column,'byte_span_zero_halfopen':[a,z],'column_one':column==1,'candidate_next_column_one':boundary})
    result={'target_ASCII':'matchMu','physical_rows':922,'LF_count':922,'literal_byte_match_count':literal_count,'ASCII_word_bounded_count':len(hits),'occurrences':hits,'interpretation':'HEURISTIC_LITERAL_COORDINATES_ONLY; may occur in comments/strings or Unicode identifiers. Next boundary is merely a later row beginning with a non-SPACE/TAB/CR/LF byte; not a declaration/owner/full-command certificate.'}
except Exception as exc:error=type(exc).__name__
for name in ('DISTINCT_AFTER','SEPARATE_FINAL'):ps.append(phase(name,roles,logical))
ok=not error and all(x['pass'] for x in ps)
out={'status':'HEURISTIC_METADATA_ONLY' if ok else 'STOP','exception_kind':error,'basis':c['basis'],'new_expectations':roles[len(book['controls']):],'phases':ps,'selected_metadata':result if ok else None,'Source_unique_delta':0,'Source_view_API_accepted':False,'defining_command_owner_accepted':False}
encoded=(json.dumps(out,separators=(',',':'))+'\n').encode();assert len(encoded)<=196608
with open(D+'R87-MATCHMU584-LITERAL-LOCATORS.metadata.json','xb') as f:f.write(encoded)
print(json.dumps({'status':out['status'],'Source_view_API_accepted':False,'defining_command_owner_accepted':False}))
raise SystemExit(0 if ok else 1)
