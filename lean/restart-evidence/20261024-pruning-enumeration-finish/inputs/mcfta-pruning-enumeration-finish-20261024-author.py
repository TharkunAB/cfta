from pathlib import Path
import json,hashlib
p=Path('/tmp/mcfta-pruning-enumeration-finish-20261024-proposal');a=Path('/tmp/mcfta-pruning-enumeration-finish-20261024');assert (a/'body-gate.json').is_file()
def fragment(name,indent=0,attachment=''):
    return ' '*indent+(p/name).read_text().rstrip('\n')+attachment+'\n'
s=fragment('context.lean.txt')+'\n'+fragment('public-complete.lean.txt',attachment=' := by')
s+='''  constructor
  · intro isEmpty
    subst result
    rfl
  · intro nonempty
'''
s+=fragment('local-source-inside.lean.txt',4,' := by')
s+='''      exact (List.getElem?_eq_some_iff.mp sourceStored).elim (fun bound storedValue => bound)
'''
s+=fragment('local-target-inside.lean.txt',4,' := by')
s+='''      exact (List.getElem?_eq_some_iff.mp targetStored).elim (fun bound storedValue => bound)
    obtain ⟨writtenHandle, middle, writtenEncoded, written, middleSame, middleStored, middleRealized⟩ :=
      SourcePruningEnumerationWrites.write_available_realized heap before result target
        (sourceScs ++ targetScs) coherent available closed realized targetInside
'''
s+=fragment('local-same-handle.lean.txt',4,' := by')
s+='''      exact Option.some.inj (writtenEncoded.symm.trans encoded)
    subst writtenHandle
    subst middle
'''
s+=fragment('local-raw.lean.txt',4,' := by')
s+='''      cases result with
      | empty => exact False.elim (nonempty rfl)
      | reference name => rfl
      | node entry edges depth free => rfl
      | union entry members depth free => rfl
      | mu entry body depthShape ordinaryShape => rfl
    refine ⟨assimilated before target source (.unenumerated (some resultHandle) (sourceScs ++ targetScs)),
      raw, rfl, ?_, ?_, ?_⟩
    · simpa only [assimilated, List.getElem?_set_ne (Ne.symm different)] using middleStored
    · exact List.getElem?_set_self (by simpa only [List.length_set] using sourceInside)
    · intro slot node scs stored
      change ((before.values.set target (.unenumerated (some resultHandle) (sourceScs ++ targetScs))).set
        source .eliminated)[slot]? = some (.unenumerated (some node) scs) at stored
      obtain old | fresh := List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored)
      · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
        exact middleRealized oldSlot node scs oldStored
      · cases fresh

end MicroCFTA.SourcePruningEnumerationFinish
'''
for name,literal in json.loads((p/'contracts.json').read_text()).items():assert s.count(literal.rstrip('\n'))==1,name
assert len(s.splitlines())<=160;(a/'SourcePruningEnumerationFinish.lean').write_text(s);print(len(s.splitlines()),len(s.encode()),hashlib.sha256(s.encode()).hexdigest())
