from pathlib import Path
import hashlib,json
area=Path('/tmp/mcfta-pruning-enumeration-cached-own-20261025')
owner=Path(str(area)+'-proposal')
assert (area/'body-gate.json').exists()
contracts=json.loads((owner/'contracts.json').read_text())
def fragment(name):return contracts[name]
def head(name):return fragment(name).rstrip('\n')
def local(name,indent):return ' '*indent+head(name)
text=fragment('context.lean.txt')+'\n'
text+=fragment('suspend-many-header.lean.txt')+'''  | [], before => some ([], before)
  | trie :: rest, before =>
      (SourcePruningEnumerationCachedChild.allocate heap none before).bind fun allocation =>
        (suspendMany heap rest allocation.2).map fun result =>
          (⟨trie, allocation.1⟩ :: result.1, result.2)

'''
text+=head('prepare-header.lean.txt')+''' :=
  if arityAllows edge.children.length scs then
    match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => none
    | some (tries, residual) =>
        (suspendMany heap tries before).map fun result =>
          [((edge.entry.key.symbol,
            edge.children.zipIdx.map (fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 result.1,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 result.1) indexed.1)),
            residual), result.2)]
  else some []

'''
text+=head('suspend-many-complete-header.lean.txt')+''' := by
  induction tries with
  | nil =>
    intro before storage realized paths counts flags
    exact ⟨before, rfl, rfl, rfl, storage.aligned, rfl, paths, storage,
      realized, counts, rfl, rfl, flags⟩
  | cons trie rest ih =>
    intro before storage realized paths counts flags
    obtain ⟨_flag, middle, _classified, nativeAllocated, _allocationRaw, middleShape,
      _middleStored, middleCounter, _middleAligned, middleForest, middlePaths,
      middleStorage, middleRealized, middleCounts, middleWaiting, _middleFlagShape,
      middleFlags⟩ := SourcePruningEnumerationCachedPrepare.allocate_complete heap none
        before roots (by intro _handle impossible; cases impossible) storage realized paths counts flags
'''
text+=local('local-middle-flags-same.lean.txt',4)+''' := by
      change some (before.core.counter,
          (⟨EnumerationState.allocated none before.core, before.expandable, before.waiting⟩ :
            EnumerationExpandableIndex.Cached Symbol EnumGuard)) =
        some (before.core.counter, middle) at nativeAllocated
      exact (congrArg (fun allocation : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard =>
        allocation.2.expandable) (Option.some.inj nativeAllocated)).symm
    obtain ⟨after, tailRun, tailShape, tailCounter, alignedAfter, forestSame, pathsAfter,
      storageAfter, realizedAfter, countsAfter, waitingSame, flagsSame, flagsAfter⟩ :=
        ih middle middleStorage middleRealized middlePaths middleCounts middleFlags
'''
text+=local('local-core-same.lean.txt',4)+''' := by
      simpa only [List.length_cons, suspendedState, middleShape] using tailShape
    refine ⟨after, ?_, coreSame, ?_, alignedAfter, forestSame.trans middleForest,
      pathsAfter, storageAfter, realizedAfter, countsAfter, waitingSame.trans middleWaiting,
      flagsSame.trans middleFlagsSame, flagsAfter⟩
    · simp only [suspendMany, nativeAllocated, Option.bind_some, tailRun, Option.map_some,
        suspendedVars, middleCounter]
    · rw [tailCounter, middleCounter, List.length_cons]
      omega

'''
text+=head('complete-header.lean.txt')+''' := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte]
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
      simp only [prepare, SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte, projected]
    | some pair =>
      obtain ⟨tries, residual⟩ := pair
      dsimp only
'''
text+=local('let-staged.lean.txt',6)+'\n'
text+='''      obtain ⟨after, ownRun, shape, grows, alignedAfter, forestSame, pathsAfter,
        storageAfter, realizedAfter, countsAfter, waitingSame, flagsSame, flagsAfter⟩ :=
          suspendMany_complete heap tries roots before storage realized paths counts flags
'''
text+=local('local-source-prefix.lean.txt',6)+''' := by
        simpa only [allowed, ↓reduceIte, projected] using
          SourcePruningEnumerationEdgePrefix.prepare_complete scs edge heap before.core
            realized storage.aligned
      obtain ⟨action, prepared, observed, _counter, _aligned, _realized⟩ := sourcePrefix
      refine ⟨action, after, prepared, ?_, ?_, shape, grows, alignedAfter, forestSame,
        pathsAfter, storageAfter, realizedAfter, countsAfter, waitingSame, flagsSame, flagsAfter⟩
      · simp only [prepare, allowed, ↓reduceIte, projected, ownRun, Option.map_some]
      · rw [shape]
        exact observed
  · simp [allowed, prepare, SourcePruningEnumerationEdgePrefix.prepare]

end MicroCFTA.SourcePruningEnumerationCachedOwn
'''
for name,literal in contracts.items():assert text.count(literal.rstrip('\n'))==1,name
assert len(text.splitlines())<=400
out=area/'SourcePruningEnumerationCachedOwn.lean';assert not out.exists();out.write_text(text)
print(json.dumps({'source':str(out),'lines':len(text.splitlines()),'bytes':len(text.encode()),'sha256':hashlib.sha256(text.encode()).hexdigest(),'all9exact':True}))
