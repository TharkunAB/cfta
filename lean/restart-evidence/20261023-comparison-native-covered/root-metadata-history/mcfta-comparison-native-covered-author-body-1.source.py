import hashlib
import json
import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

gate = load(HERE / 'root-declaration-review.json')
assert gate['status'] == 'ROOT_ACCEPTED' and gate['proof_body_authorized']
assert gate['whole_source_cap'] == 230 and gate['private_helpers'] == [] and not gate['induction']
plan = HERE / 'signature-plan'
context = (plan / 'context.lean.txt').read_text()
header = (plan / 'public-header.lean.txt').read_text().rstrip('\n')
body = '''  classical
  dsimp only
  let inventory : List IntersectionFlatMemoKeyDomain.DomainKey :=
    SourceRecursiveIntersectionSourceInventory.domains source
  let ordered : Edge × Edge := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
  let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
  obtain ⟨fuel, result, after, done, resident, law, afterGood, afterContextual,
    afterSemantic, extension, afterStable, afterIdle, tables, retained, afterAllocations⟩ :=
    SourceCurrentSameSymbolEdgeComparisonDomains.original_rows_complete bits source facts formulas solver
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
      leftParent rightParent leftOriginal rightOriginal leftAvailable rightAvailable
      leftClosed rightClosed left right leftMember rightMember symbols initialDomains initialValid
      before stable good contextual semantic growth history allocations idle room
  have finalCovered : Covered inputs after.checked.native := by
    by_cases present :
      (∃ handle, before.memo.table (left.entry.identity, right.entry.identity) = some handle) ∨
      (∃ handle, before.memo.table (right.entry.identity, left.entry.identity) = some handle)
    ·
      have hitChecked : after.checked = before.checked := by
        exact SourceCurrentSameSymbolEdgeHitReadback.completed_hit_checked
          (view source (guardHolds formulas solver))
          (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
          (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
          (guardHolds formulas solver) fuel left right result before after stable present done
      simpa only [hitChecked] using covered
    ·
      have missing : before.memo.table (left.entry.identity, right.entry.identity) = none := by
        cases found : before.memo.table (left.entry.identity, right.entry.identity) with
        | none => rfl
        | some handle => exact False.elim (present (Or.inl ⟨handle, found⟩))
      have reverseMissing : before.memo.table (right.entry.identity, left.entry.identity) = none := by
        cases reverseFound : before.memo.table (right.entry.identity, left.entry.identity) with
        | none => rfl
        | some handle => exact False.elim (present (Or.inr ⟨handle, reverseFound⟩))
      have leftInputs : ∀ child ∈ left.children,
          Original child ∧ inputs.valid (inputOf child) := by
        exact (SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts
          (guardHolds formulas solver)
          (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
          leftParent left leftOriginal leftAvailable leftClosed leftAdmitted leftMember).1
      have rightInputs : ∀ child ∈ right.children,
          Original child ∧ inputs.valid (inputOf child) := by
        exact (SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts
          (guardHolds formulas solver)
          (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
          rightParent right rightOriginal rightAvailable rightClosed rightAdmitted rightMember).1
      have rawScope : EdgeScope source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := by
        refine ⟨resident_edges source facts.linked leftParent leftAvailable.resident left leftMember,
          resident_edges source facts.linked rightParent rightAvailable.resident right rightMember,
          ?_, ?_, ?_⟩
        · intro child member
          exact (leftInputs child member).1
        · intro child member
          exact (rightInputs child member).1
        · intro _ member
          cases member
      have rawCovered : EdgeCovered inputs ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := by
        exact ⟨⟨leftInputs, rightInputs⟩,
          SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
      have orderedInputs : EdgeScope source request ∧ EdgeCovered inputs request := by
        by_cases swap : right.entry.identity < left.entry.identity
        · simp only [request, ordered, swap, ↓reduceIte]
          exact ⟨⟨rawScope.rightResident, rawScope.leftResident,
            rawScope.right, rawScope.left, rawScope.bindings⟩,
            ⟨⟨rightInputs, leftInputs⟩,
              SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩⟩
        · simpa only [request, ordered, swap, ↓reduceIte] using And.intro rawScope rawCovered
      have ready : EdgeReady before.checked.native.machine request := by
        exact ⟨empty_domain _, edge_grows source _ growth _ orderedInputs.1.leftResident,
          edge_grows source _ growth _ orderedInputs.1.rightResident⟩
      have fields : Fields (.edgeBody request .pure) before.checked := by
        exact ⟨ready, fun _ => True.intro⟩
      have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources
          bits source inventory initialDomains := by
        exact ⟨facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts,
          initialValid, room.1, room.2.1, Nat.lt_of_le_of_lt (Nat.le_add_right _ _) room.2.2⟩
      have current : SourceCurrentAllocatedRecursivePrefixState.Current
          source inventory initialDomains before.checked := by
        exact ⟨good, semantic, growth, history, allocations⟩
      have physicalCertificate : SourceCurrentAllocatedRecursivePrefixControl.Certified
          source inventory (.edgeBody request .pure) before.checked.native.machine
          (fun final value => EdgeResident final.heap value) := by
        exact SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request
          before.checked.native.machine orderedInputs.1
          (SourceRecursiveIntersectionSourceInventory.empty_mem source) ready
      have admissionCertificate : ControlCertified source (guardHolds formulas solver) inputs
          (.edgeBody request .pure) before.checked.native.machine
          (fun final value => EdgeResident final.heap value) := by
        refine ⟨orderedInputs.1, orderedInputs.2, ?_⟩
        intro _ _ _ _ _ resident
        exact resident
      obtain ⟨nativeFuel, _, steps, _, _, _, _⟩ :=
        SourceCurrentSameSymbolEdgeControl.miss_readback fuel left right result before after
          (FlatMemoThunk.Valid.map before.memo _ _ _ stable.valid (fun _ _ => True.intro))
          missing reverseMissing done
      have physicalRun : SourceCurrentAllocatedRecursivePrefixReceipt.Receipt
          source inventory initialDomains nativeFuel (.edgeBody request .pure) before.checked
          (.code (.pure result)) after.checked (fun final value => EdgeResident final.heap value) := by
        exact SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources nativeFuel
          (.edgeBody request .pure) before.checked (.code (.pure result)) after.checked
          (fun final value => EdgeResident final.heap value) current physicalCertificate fields steps
      exact (SourceCurrentAllocatedNativeAdmissionTrace.Trace.covered source
        (guardHolds formulas solver) inputs
        (SourceCurrentAllocatedNativeCoveredQuery.branches source facts (guardHolds formulas solver) inputs)
        physicalRun.trace (fun final value => EdgeResident final.heap value)
        good semantic growth history fields covered admissionCertificate).1
  exact ⟨fuel, result, after, done, resident, law, afterGood, afterContextual,
    afterSemantic, extension, afterStable, afterIdle, tables, retained, afterAllocations, finalCovered⟩
'''
source = context + '\n' + header + ' := by\n' + body + '\nend MicroCFTA.' + NAME + '\n'
assert len(source.splitlines()) <= 230
assert 'sorry' not in source and 'set_option' not in source and 'private theorem' not in source
positions = []
for fragment in load(plan / 'insertion-map.json')['compiled_fragments']:
    value = (plan / fragment['file']).read_text().rstrip('\n')
    if 'future_body_attachment' in fragment:
        value += fragment['future_body_attachment']
    assert source.count(value) == 1, fragment['file']
    positions.append(source.index(value))
assert positions == sorted(positions)
target = Path('/tmp/mcfta-comparison-native-covered-source')
assert not target.exists()
target.mkdir()
raw = source.encode()
(target / (NAME + '.lean')).write_bytes(raw)
ledger = dict(status='SOURCE_ONLY_PENDING_INDEPENDENT_BODY_REVIEW', author='root',
    source=NAME + '.lean', lines=len(source.splitlines()), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest(),
    accepted_declaration_gate=sha(HERE / 'root-declaration-review.json'), whole_source_cap=230,
    exact_fragments=25, public_heads=['original_rows_complete'], private_helpers=[], induction=False,
    H15_invocations=1, all_twelve_H15_outputs_retained=True, appended_native_Covered=True,
    compiler_jobs=0, whole_goal_complete=False)
(target / 'source-ledger.json').write_text(json.dumps(ledger, indent=2) + '\n')
pins = []
for path in sorted(target.iterdir()):
    data = path.read_bytes()
    pins.append(dict(path=path.name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(target / 'FROZEN.json').write_text(json.dumps(dict(status='SOURCE_ONLY_FROZEN',
    pins_sha256=sha(target / 'pins.json'), compiler_jobs=0), indent=2) + '\n')
print(json.dumps(dict(status='PASS', **{key:ledger[key] for key in ['lines','bytes','sha256']},
    pins_sha256=sha(target / 'pins.json'), frozen_sha256=sha(target / 'FROZEN.json'))))
