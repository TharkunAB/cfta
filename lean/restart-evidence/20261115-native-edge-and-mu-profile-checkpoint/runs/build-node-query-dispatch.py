from pathlib import Path
import hashlib

packet = Path('lean/restart-evidence/20261115-current-node-query-dispatch-origin-draft')
source = Path('lean/MicroCFTA/SourceCurrentAllocatedNativeCompileDispatchOrigin.lean')
assert hashlib.sha256(source.read_bytes()).hexdigest() == '5ede4cb6ae69f17d711f4aad652b5282c658a296f5364ebdd0c97dbeb24abdea'
text = source.read_text()
text = text[:text.index('/-- The observed node finish has an actual compiled producer')]
text = text.replace('SourceCurrentAllocatedNativeCompileDispatchOrigin',
                    'SourceCurrentAllocatedNativeNodeQueryDispatchOrigin')
text = text.replace('import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion\n',
    'import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion\n'
    'import MicroCFTA.SourceCurrentNativeEnterCommonOperand\n'
    'import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit\n')
old = '''    resume value = rest

private theorem origin_prepend'''
new = '''    resume value = rest ∧
    ∃ (queryUsed : Nat) (queryBefore : Checked width)
      (original : NodeRequest Symbol Guard)
      (chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      used = queryUsed + 1 ∧
      Steps queryUsed control before (.code (.node original resume)) queryBefore ∧
      lookupNode width original queryBefore.native = (.memoized handle, chosen) ∧
      demandNode handle chosen = (.evaluate request, running) ∧
      beforeBody = ⟨running, queryBefore.operations⟩

private theorem origin_prepend'''
assert old in text
text = text.replace(old, new)
old = '''  obtain ⟨first, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last⟩ := known
  exact ⟨used + first, bodyCount, beforeBody, resume, by omega, by omega,
    actual.trans _ _ _ _ _ _ _ _ entered, owner, bodyTrace, last⟩'''
new = '''  obtain ⟨first, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last,
    queryUsed, queryBefore, original, chosen, running, counted, queryPrefix, selected, demanded, stateEq⟩ := known
  refine ⟨used + first, bodyCount, beforeBody, resume, by omega, by omega,
    actual.trans _ _ _ _ _ _ _ _ entered, owner, bodyTrace, last,
    used + queryUsed, queryBefore, original, chosen, running, by omega, ?_, selected, demanded, stateEq⟩
  exact actual.trans _ _ _ _ _ _ _ _ queryPrefix'''
assert old in text
text = text.replace(old, new)
old = '''  obtain ⟨used, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last⟩ := known
  refine ⟨used, bodyCount, beforeBody, fun result => (resume result).bind outside,
    total, positive, ?_, owner, bodyTrace, ?_⟩'''
new = '''  obtain ⟨used, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last,
    queryUsed, queryBefore, original, chosen, running, counted, queryPrefix, selected, demanded, stateEq⟩ := known
  refine ⟨used, bodyCount, beforeBody, fun result => (resume result).bind outside,
    total, positive, ?_, owner, bodyTrace, ?_, ?_⟩'''
assert old in text
text = text.replace(old, new)
old = '''  · change (resume value).bind outside = rest.bind outside
    rw [last]

private theorem steps_shape'''
new = '''  · change (resume value).bind outside = rest.bind outside
    rw [last]
  · refine ⟨queryUsed, queryBefore, original, chosen, running, counted, ?_, selected, demanded, stateEq⟩
    have lifted := queryPrefix.bind _ _ _ _ _ outside
    simpa only [Control.bind, Code.bind] using lifted

private theorem first_inputs
    {count : Nat} {control final : Control A} {before after : Checked width}
    (actual : Trace count control before final after) (positive : 0 < count) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs control before := by
  cases actual with
  | refl => omega
  | cons _ _ _ _ _ _ _ inputs _ _ => exact inputs

private theorem steps_shape'''
assert old in text
text = text.replace(old, new)
old = '''                            by omega, by omega, .cons _ _ _ _ _ _ 0 one (.refl _ _), started, bodyTrace, rfl⟩'''
new = '''                            by omega, by omega, .cons _ _ _ _ _ _ 0 one (.refl _ _), started, bodyTrace, rfl,
                            0, before, request, chosen, running, rfl, .refl _ _, selected, demanded, rfl⟩'''
assert text.count(old) == 1
text = text.replace(old, new)
header = (packet / 'PUBLIC-HEADER.lean.txt').read_text()
proof = (packet / 'PUBLIC-PROOF.lean.txt').read_text()
result = text + '/-- Recover the actual query event and its same-state isolated dispatch before the observed finish. -/\n' + header + proof
(packet / 'SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.lean').write_text(result)
assert result[result.index('theorem actual_node_query_dispatch_from_initial_query_finish\n'):].startswith(header)
(packet / 'PROBES.lean.txt').write_text(
    '#check @MicroCFTA.SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_initial_query_finish\n'
    '#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_initial_query_finish\n')
print({'raw_lines': len(result.splitlines()), 'raw_sha256': hashlib.sha256(result.encode()).hexdigest()})
