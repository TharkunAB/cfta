from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');area=Path('/tmp/mcfta-recursive-callback-one-20261026')
def signature(file,name):
 text=(root/file).read_text();start=text.index('theorem '+name);return text[start:text.index(' := by',start)]
old=signature('SourcePruningEnumerationRecursiveCallback.lean','callback_complete')
old=old[old.index('      Packet formulas'):].strip()
new=signature('SourcePruningEnumerationCallbackOneResources.lean','callback_one_complete_resources')
start=new.index('      Packet formulas');group=new.index('      (∀ extra,',start)
finish=new.index(' ∧\n      (∀ extra, continueWith',group)
retained=new[start:group]+new[group+7:finish-1]
old=old.replace('Caller width','Caller (bits + 2)')
normal=lambda text:re.sub(r'\s+','',text)
assert normal(old)==normal(retained)
folder=area/'contract-evidence';folder.mkdir(exist_ok=True)
(folder/'callback-earlier-specialized.txt').write_text(old+'\n');(folder/'callback-retained.txt').write_text(retained+'\n')
result={'exact_without_whitespace':True,'characters':len(normal(old)),'bytes':len(normal(old).encode()),'sha256':hashlib.sha256(normal(old).encode()).hexdigest()}
(folder/'contract.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
