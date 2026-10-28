from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-selected-value-caller-20261028')
def decl(name,theorem):
 b=(root/'lean/MicroCFTA'/(name+'.lean')).read_bytes();s=b.index(('theorem '+theorem).encode());return b[s:b.index(b' := by',s)]
old=decl('SourcePruningEnumerationSelectedValue','run_complete');new=decl('SourcePruningEnumerationSelectedValueCaller','complete');oldret=old[old.index('    ∃ '.encode()):];newret=new[new.index('    ∃ '.encode()):];native=newret[:newret.rindex(b'\n      Post ')];native=native.replace(b'      ((',b'      (',1);assert native.endswith(b') \xe2\x88\xa7');native=native[:-5]
native=native.replace(b'SourcePruningEnumerationSelectedValue.run',b'run').replace(b'before.checked.native.machine.heap',b'before');native=re.sub(rb'\bheap\b',b'after',native)
assert re.sub(rb'\s+',b'',native)==re.sub(rb'\s+',b'',oldret),(native,oldret)
(a/'root-contracts/native-old-result.txt').write_bytes(oldret);(a/'root-contracts/caller-native-result-recovered.txt').write_bytes(native)
(a/'root-native-packet-comparison.json').write_text(json.dumps({'status':'pass','entire_original_native_result_retained_modulo_layout_and_specialization':True,'old_result_bytes':len(oldret),'old_result_sha256':hashlib.sha256(oldret).hexdigest(),'scope':'Remove final Post and outer native grouping; invert native qualification, original heap specialization and returned heap name; ignore whitespace. Original caller admission remains Context/Available/closed, not generic old native admission.'},indent=2)+'\n');print('Full original native result independently recovered.')
