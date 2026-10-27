from pathlib import Path
import hashlib,json,datetime
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-recursive-admission-20261027/selected-receipt-language-draft');sha=lambda b:hashlib.sha256(b).hexdigest();sources=[];cuts=[]
def add(name,spans=(),theorems=(),scope='whole direct API contract read'):
 p=repo/'lean/MicroCFTA'/(name+'.lean');raw=p.read_bytes();s=raw.decode();snapshot='inputs/lean/MicroCFTA/'+name+'.lean';q=out/snapshot;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
 sources.append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=sha(raw),read_scope=scope))
 pairs=list(spans)
 for theorem in theorems:
  start=s.index('theorem '+theorem);end=s.index(' := by',start)+len(' := by');pairs.append((s[:start].count('\n')+1,s[:end].count('\n')+1))
 lines=raw.splitlines(keepends=True)
 for start,end in pairs:
  assert 1<=start<=end<=len(lines)
  b=b''.join(lines[start-1:end]);snapshot=f'cuts/{name}--{start}-{end}.lean';q=out/snapshot;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  cuts.append(dict(path=str(p),source=str(p),snapshot=snapshot,start=start,end=end,source_sha256=sha(raw),bytes=len(b),sha256=sha(b)))
add('SourcePruningEnumerationPrefixCanonicalHistory',theorems=['prefix_canonical'],scope='whole actual prefix_canonical theorem and retained-action proof reviewed; later wrapper is context only')
add('SourcePruningEnumerationPrefixLanguage',spans=[(32,59)],theorems=['prefix_semantics'],scope='PrefixMeaning and whole actual prefix_semantics proof/direct helpers read')
add('SourcePruningEnumerationRecursivePrefixLanguage',theorems=['packet_selected_ready'],scope='whole packet_selected_ready proof and original packet prefix semantic wrapper read')
add('SourcePruningEnumerationPrefixPacket',theorems=['prefix_cache_valid'],scope='whole cache/post transport source read')
add('SourcePruningEnumerationRecursivePacket',spans=[(21,35)],scope='whole unchanged Packet source and transport API read')
add('SourcePruningEnumerationOrdinaryReceiptLanguage',theorems=['CompletedHeadReceipt.sound_ordinary_callback_input'],scope='whole checked consumer proof read at final strict3 identity')
add('SourcePruningEnumerationObservedFramesLanguage',theorems=['enter_semantics','recordTypes_success_semantics'],scope='whole actual entry/callback fixed-heap frame semantic proof read')
add('SourcePruningEnumerationPrefixCompletion',spans=[(20,47)],scope='PrefixValid definition and original completion producer contracts reviewed; unrelated proof repetition not freshly audited')
add('SourcePruningEnumerationSelectedStep',spans=[(27,94)],scope='actual Result and whole runPrefix body read; unrelated finish proof not freshly reaudited')
index=dict(version=1,status='OPEN DRAFT; ROOT CHECK PENDING',created=datetime.datetime.now().astimezone().isoformat(),sources=sources,cuts=cuts,read_scope='report.txt; nine bounded direct source/API inputs, not a full import-closure audit',new_compiler_checks_executed=False)
(out/'source-pins.json').write_text(json.dumps(index,indent=2)+'\n')
print(json.dumps(dict(sources=len(sources),cuts=len(cuts),cut_lines=sum(c['end']-c['start']+1 for c in cuts)),indent=2))
