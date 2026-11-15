from pathlib import Path
import datetime
import hashlib
import json

base = Path('lean/restart-evidence')
packet = base / '20261115-current-general-m-union-finish-draft'
ordinary = (base / '20261115-current-general-m-ordinary-explicit-entry-control-repair/SourceCurrentAllocatedNativeGeneralMOrdinaryFinish.lean').read_text()
start = ordinary.index('  have initialPhysical :')
stop = ordinary.index('  obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,', start)
common = ordinary[start:stop]
proof = r'''  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _sourceFacts⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyEq]
    exact ⟨.node bodyEntry.identity, rfl⟩
  obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
      operandProfile, operandHeight, strictAlias, ordered⟩ := qualified
  obtain ⟨unionEntry, members, level, free, unionSide⟩ := unionOperand
  have aliasNotUnion : openAlias ≠ .union unionEntry members level free := by
    rcases aliasKind with same | same
    · rw [same, bodyEq]
      intro impossible
      cases impossible
    · rw [same]
      intro impossible
      cases impossible
  have operandEq : operand = .union unionEntry members level free := by
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · rcases unionSide with same | same
      · exact (aliasNotUnion (left.symm.trans same)).elim
      · exact right.symm.trans same
    · rcases unionSide with same | same
      · exact left.symm.trans same
      · exact (aliasNotUnion (right.symm.trans same)).elim
  subst operand
  obtain ⟨useReference, aliasEq⟩ : ∃ useReference : Bool,
      openAlias = (if useReference then .reference (.interned entry.identity) else body) := by
    rcases aliasKind with same | same
    · exact ⟨false, same⟩
    · exact ⟨true, same⟩
  let alias : Node := if useReference then .reference (.interned entry.identity) else body
  have aliasChoice : alias = body ∨ alias = .reference (.interned entry.identity) := by
    cases useReference with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl
  have orderedAlias :
      ((request.left = alias ∧ request.right = .union unionEntry members level free) ∨
        (request.left = .union unionEntry members level free ∧ request.right = alias)) := by
    simpa only [aliasEq] using ordered
  obtain ⟨aliasFirst, leftEq, rightEq⟩ : ∃ aliasFirst : Bool,
      request.left = (if aliasFirst then alias else .union unionEntry members level free) ∧
      request.right = (if aliasFirst then .union unionEntry members level free else alias) := by
    rcases orderedAlias with ⟨left, right⟩ | ⟨left, right⟩
    · exact ⟨true, left, right⟩
    · exact ⟨false, left, right⟩
  have referenceBound : useReference = true →
      height (.union unionEntry members level free) < height pattern := by
    intro used
    apply strictAlias
    rw [aliasEq, used]
    rfl
  have originalEntry := authentic
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed,
      entryBefore, entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, allocationEq, _entryOne, domainEq⟩ := entryData
  let universeValue : Node := .mu entry body depth ordinary
  let actualEntered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey
    (if universeFirst then universeValue else pattern)
    (if universeFirst then pattern else universeValue)
    (if universeFirst then entry.identity else patternId)
    (if universeFirst then patternId else entry.identity)
  have domainOrdered : request.domain = actualEntered.1 :=
    domainEq.trans (congrArg Prod.fst allocationEq).symm
  let desired : NodeRequest Symbol Guard := ⟨actualEntered.1,
    if aliasFirst then alias else .union unionEntry members level free,
    if aliasFirst then .union unionEntry members level free else alias⟩
  have requestEq : request = desired := by
    cases request with
    | mk domain left right =>
        change domain = actualEntered.1 at domainOrdered
        change left = _ at leftEq
        change right = _ at rightEq
        simp only [desired, domainOrdered, leftEq, rightEq]
  subst request
  have raw := SourceCurrentAllocatedNativeMixedUnionProfile.current_stored_universe_mixed_union_body_profile_of_fuel_induction
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    pattern patternClosed patternId patternIdentity patternKind
    unionEntry members level free operandProfile operandHeight useReference aliasFirst universeFirst referenceBound
    (.code (.node rootRequest .pure)) (⟨initial width machine, operations⟩ : Checked width)
    entryBefore queryBefore beforeBody reader initialPhysical sourceGrowth
    wholeCount entryUsed queryUsed rest wholeActual (by omega) entryNext entryPrefix.steps
  dsimp only at raw
  refine (raw queryResume queryOrigin (fuel - queryUsed) bodyCount value beforeFinish
    (fun emitted => .finishNode handle emitted (.pure emitted))
    queryOperations queryInputs queryFields isolatedDispatch (by omega) (by omega) rawBody ?_).1
  intro closedOperand child used childFuel childCount _positive _smaller _fuelSpan
    _rawSmaller actualSpan childDomain ownProfile childHeight strictChild orderedChild
    next first last emitted origin _childPhysical _childGrowth _childOperations _childInputs
    _childFields _leftAvailable _rightAvailable childActual
  have childQualified : MixedQualified (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary child := by
    refine ⟨pattern, patternId, alias, closedOperand, ?_, aliasChoice, ownProfile,
      childHeight, strictChild, orderedChild⟩
    rw [childDomain]
    exact originalEntry
  obtain ⟨childKey, keyed⟩ := SourceCurrentAllocatedNativeGeneralCMHistory.qualified_key
    rootRequest machine operations wholeCount entry body depth ordinary bodyCodec child (Or.inr childQualified)
  have lifted := origin.bind _ _ _ _ _ queryResume
  have globalOrigin : Steps (queryUsed + used) (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestNode child.domain child.left child.right).bind
        (fun result => (next result).bind queryResume))) first := by
    simpa only [Control.bind, Code.bind_assoc] using
      queryOrigin.trans _ _ _ _ _ _ _ _ lifted
  have observed := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_node_finish
    (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
    (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
    rootRequest machine machineValid operations fuel finishUsed (queryUsed + used) childCount
    handle value parentNext beforeFinish (by omega) actual past child childKey keyed
    (fun result => (next result).bind queryResume) first last emitted (by omega) globalOrigin childActual
  exact observed.1.2 childQualified
'''
header = (packet / 'PUBLIC-HEADER.lean.txt').read_text()
assert hashlib.sha256(header.encode()).hexdigest() == '61f9fce2ef57f043faa048ce51685459777684364af01d9f8de4e323acb3f997'
source = (packet / 'PREAMBLE.lean.txt').read_text() + header + common + proof
source += '\nend MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish\n'
(packet / 'SourceCurrentAllocatedNativeGeneralMUnionFinish.lean').write_text(source)
(packet / 'PROBES.lean.txt').write_text('#check @MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish.mixed_union_profile_at_actual_node_finish\n#print axioms MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish.mixed_union_profile_at_actual_node_finish\n')
(packet / 'SCOPE.md').write_text('# Status\n\nUNCOMPILED. The actual mixed union case retains full original P and both\nreal entry orientations on the same fixed whole T. Each raw callback\nhas a genuine count bound from the observed body. The proof derives the\nchild qualification, key, same-root prefix and actual returned-cell law\nfrom the exact beforeFinish C/M invariant. Full native history is open.\n')
print(json.dumps({'at': datetime.datetime.now().astimezone().isoformat(),
                  'raw': hashlib.sha256(source.encode()).hexdigest(),
                  'lines': len(source.splitlines()), 'full_header_unchanged': True}))
