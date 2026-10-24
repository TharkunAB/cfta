from pathlib import Path
import json,hashlib,difflib
p=Path('/tmp/mcfta-pruning-enumeration-dispatch-20261024-proposal-v3')
a=Path('/tmp/mcfta-pruning-enumeration-dispatch-20261024')
source=a/'SourcePruningEnumerationDispatch.lean'
old=source.read_text(); (a/'draft-before-layout.lean.txt').write_text(old)
def frag(name,indent=0): return ' '*indent+(p/name).read_text().rstrip('\n')
head=frag('public-dispatch.lean.txt')
start=old.index(head)+len(head); end=old.index('\n\n/-- Safe raw entries',start)
body=' := Id.run do\n'+frag('definition-noop.lean.txt',2)+''' := fun state => [.ok ((), state)]
  if source = target then return (.ok (some noop), beforeCaller, queries)
  let some sourceValue := before.values[source]? | return (.ok none, beforeCaller, queries)
  match sourceValue with
  | .eliminated => return (.ok (some noop), beforeCaller, queries)
  | _ => pure ()
  let some targetValue := before.values[target]? | return (.ok none, beforeCaller, queries)
  let .unenumerated sourceNode sourceScs := sourceValue |
    return (.ok (some (failure .invalidIntersection)), beforeCaller, queries)
  let .unenumerated targetNode targetScs := targetValue |
    return (.ok (some (failure .invalidIntersection)), beforeCaller, queries)
  let some sourceHandle := sourceNode |
    return (.ok (some (finishOptional source target targetNode sourceScs targetScs)), beforeCaller, queries)
  let some targetHandle := targetNode |
    return (.ok (some (finishOptional source target (some sourceHandle) sourceScs targetScs)), beforeCaller, queries)
  let some left := lookupNode beforeCaller.checked.native.machine.heap sourceHandle |
    return (.ok none, beforeCaller, queries)
  let some right := lookupNode beforeCaller.checked.native.machine.heap targetHandle |
    return (.ok none, beforeCaller, queries)
'''+frag('definition-actual.lean.txt',2)+''' :=
    SourceEqualityNativeDemand.execute nativeFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked
  match actual with
  | .done query queried =>
'''+frag('definition-prepared.lean.txt',4)+''' :=
      afterQuery checkEmpty p h source target sourceScs targetScs query queried beforeCaller queries
    return (prepared.1.mapError Sum.inr, prepared.2.1, prepared.2.2)
  | other => return (.error (.inl other),
      SourceCurrentAllocatedPartialState.advance beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries)'''
new=old[:start]+body+old[end:]
for name,literal in json.loads((p/'contracts.json').read_text()).items(): assert new.count(literal.rstrip('\n'))==1,name
source.write_text(new)
(a/'prestrict-layout-forward.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='initial-root-draft',tofile='strict-1-input')))
(a/'prestrict-layout-note.md').write_text('The first author draft nested the prepared let below its frozen continuation indentation. The source was not compiled. The selected draft uses existing Id.run for local early returns. It retains the same three definitions and theorem, literal contracts, result types, source branch priority and checked operations. It adds no instance or shared error/state monad. The complete initial draft and exact patch remain. This is a source-only layout correction, not a compiler, cap or seal failure.\n')
print(json.dumps({'source':str(source),'lines':len(new.splitlines()),'bytes':len(new.encode()),'sha256':hashlib.sha256(new.encode()).hexdigest(),'contracts_exact':23}))
