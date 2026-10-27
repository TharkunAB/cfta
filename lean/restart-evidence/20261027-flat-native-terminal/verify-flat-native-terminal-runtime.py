from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
area=Path('/tmp/mcfta-flat-native-terminal-20261027')
def data(name):return (root/(name+'.lean')).read_text()
def declaration(text,name):
 start=re.search(r'^(?:noncomputable )?def '+name+r'\b',text,re.M).start()
 tail=text[start:]
 end=re.search(r'\n(?:/--|private |theorem |end |local notation)',tail)
 return tail[:end.start()].strip() if end else tail.strip()
def hashtext(text):return hashlib.sha256(text.encode()).hexdigest()
records=[]
def verify(label,old,new,changes):
 assert old==new,label
 records.append({'block':label,'result':'exact after stated substitutions','sha256':hashtext(new),'bytes':len(new.encode()),'substitutions':changes})
old=declaration(data('SourcePruningEnumerationIncomingNode'),'run')
old=old[old.index('      match before.values[found.representative]? with'):]
old='\n'.join(line[4:] if line.startswith('    ') else line for line in old.splitlines()).replace('found.representative','target').replace('readState','before')
new=declaration(data('EnumerationFlatNativeIncoming'),'run')
new=new[new.index('  match before.values[target]? with'):]
verify('incoming native slot/query/check suffix',old,new,['remove four outer indentation spaces','found.representative becomes direct target','old readState becomes unchanged flat before'])
for function in ['adapt','run']:
 old=declaration(data('SourcePruningEnumerationIncomingCacheAdapter'),function)
 for a,b in [('EnumerationExpandableIndex.Cached','EnumerationFlatCached.Cached'),('EnumerationState.State','EnumerationFlatState.State'),('EnumerationExpandableIndex.frame','EnumerationFlatCached.frame'),('SourcePruningEnumerationNativeIndex.write','EnumerationFlatNativeIndex.write')]:old=old.replace(a,b)
 old=old.replace('(indexFuel target : Nat)','(target : Nat)').replace('(representativeFuel nativeFuel p h indexFuel : Nat)','(nativeFuel p h : Nat)').replace('SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel','EnumerationFlatNativeIncoming.run checkEmpty nativeFuel').replace('heap indexFuel target','heap target')
 verify('incoming cache '+function,old,declaration(data('EnumerationFlatNativeIncomingCache'),function),['flat core/cache/frame/write types','remove old representative and count fuel','use actual flat incoming worker'])
old=declaration(data('SourcePruningEnumerationCachedTerminalAdapter'),'run')
for a,b in [('EnumerationExpandableIndex.Cached','EnumerationFlatCached.Cached'),('EnumerationState.State','EnumerationFlatState.State'),('EnumerationExpandableIndex.frame','EnumerationFlatCached.frame'),('SourcePruningEnumerationCachedFold.run','EnumerationFlatNativeCachedFold.run'),('SourcePruningEnumerationIncomingNode.run','EnumerationFlatNativeIncoming.run'),('SourcePruningEnumerationIncomingCacheAdapter.run','EnumerationFlatNativeIncomingCache.run')]:old=old.replace(a,b)
old=old.replace('(representativeFuel nativeFuel p h indexFuel : Nat)','(nativeFuel p h : Nat)').replace('ExceptT.run (SourcePruningEnumerationTerminalPrefix.run\n        representativeFuel first rest','ExceptT.run (EnumerationFlatTerminalPrefix.run\n        first rest').replace('checkEmpty representativeFuel nativeFuel','checkEmpty nativeFuel').replace('                    indexFuel foldCaller','                    foldCaller')
start=old.index('            match incomingObserved with');end=old.index('          | stoppedRaw',start)
wrap=declaration(data('EnumerationFlatNativeTerminal'),'wrapIncoming')
wrapbody=wrap[wrap.index('match observed with'):].strip()
oldwrap='\n'.join(line[12:] for line in old[start:end].replace('incomingObserved','observed').splitlines()).strip()
verify('terminal incoming result wrapper',oldwrap,wrapbody,['extract the same incoming match as pure wrapIncoming'])
old=old[:start]+'            wrapIncoming winner moved incomingObserved\n'+old[end:]
verify('terminal adapter runtime',old,declaration(data('EnumerationFlatNativeTerminal'),'run'),['flat core/cache/frame/prefix/fold/incoming modules','remove old representative and count fuel','extract exact incoming result wrapper'])
(area/'runtime-mirror-validation.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'result':'pass','runtime_blocks':len(records)}))
