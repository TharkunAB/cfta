from pathlib import Path
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');out=Path('/tmp/mcfta-resource-captured-20261027/captured-route-review/drafts')
text=(repo/'SourcePruningEnumerationSelectedEdgeStableNeutral.lean').read_text()
text=text.replace('import MicroCFTA.SourcePruningEnumerationSelectedEdge\n','import MicroCFTA.SourcePruningEnumerationSelectedEdgeResources\n')
text=text.replace('import MicroCFTA.SourcePruningEnumerationTraversalLanguage\n','import MicroCFTA.SourcePruningEnumerationTraversalResourceLanguage\n')
text=text.replace('import MicroCFTA.SourcePruningEnumerationTraversalStableNeutral\n','import MicroCFTA.SourcePruningEnumerationTraversalStableResourceNeutral\n')
text=text.replace('# Neutral assignment restrictions of a completed selected edge','# Neutral selected-edge restrictions from original resources')
text=text.replace('The actual own-class prefix supplies the traversal input cache.','The actual own-class prefix supplies the traversal input cache.\nThe original reservation covers each actual child bucket.')
text=text.replace('open SourceCurrentAllocatedPartialInvariant (Context Post)\n','open SourceCurrentAllocatedPartialInvariant (Context Post)\nopen SourcePruningEnumerationIncomingReservation (Seed Reserved)\nopen SourceCurrentConstrainedCapGeneratedQueryResources (Fits)\n')
text=text.replace('local notation "Fragment" => Fragments.Fragment Symbol\n','local notation "Fragment" => Fragments.Fragment Symbol\nlocal notation "Heap" => SourceEqualityAnnotationHeap.Heap\n')
text=text.replace('variable {width : Nat}','variable {bits : Nat}').replace('Caller width','Caller (bits + 2)')
text=text.replace('theorem stable_complete_neutral_semantics\n','theorem stable_complete_neutral_semantics_resources\n    (seed : Seed)\n')
text=text.replace('    (ranges : Ranges checkEmpty scs edge caller before memos.query)\n','    (fits : Fits seed.2 caller.checked)\n    (reserved : Reserved bits seed (cost edge scs before.core.counter tries))\n    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)\n')
old='''  have numeric : SourcePruningEnumerationTraversalCompletion.Ranges checkEmpty inputs caller own memos.query := by
    have admitted := ranges edge.entry.key.symbol _ residual own ownRun
    rwa [readback] at admitted
'''
assert old in text;text=text.replace(old,'')
text=text.replace('    _pendingHistory, _fragmentBounds, shape, _childMeaning⟩ :=','    _pendingHistory, _fragmentBounds, shape, _returnedFits, _returnedKnown, _childMeaning⟩ :=')
text=text.replace('SourcePruningEnumerationTraversalCompletion.complete_with_fragments_semantics\n      formulas','SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_semantics\n      seed formulas')
text=text.replace('initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine numeric','initial ownSafe ownPaths ownCounts ownFlags ownRealized genuine fits reserved known')
text=text.replace('SourcePruningEnumerationTraversalCompletion.stable_complete_neutral_semantics\n      formulas','SourcePruningEnumerationTraversalCompletion.stable_complete_neutral_semantics_resources\n      seed formulas')
text=text.replace('ownRealized genuine numeric','ownRealized genuine fits reserved known')
assert 'ranges' not in text and 'numeric' not in text
(out/'SourcePruningEnumerationSelectedEdgeStableResourceNeutral.lean').write_text(text)
text=(repo/'SourcePruningEnumerationSelectedEdgeNeutralSoundness.lean').read_text()
text=text.replace('import MicroCFTA.SourcePruningEnumerationSelectedEdgeStableNeutral\n','import MicroCFTA.SourcePruningEnumerationSelectedEdgeStableResourceNeutral\n')
text=text.replace('# Native soundness with the captured root payload neutralized','# Resource-based soundness with the captured root neutralized')
text=text.replace('open SourceCurrentAllocatedPartialInvariant (Context Post)\n','open SourceCurrentAllocatedPartialInvariant (Context Post)\nopen SourcePruningEnumerationIncomingReservation (Seed Reserved)\nopen SourceCurrentConstrainedCapGeneratedQueryResources (Fits)\n')
text=text.replace('local notation "Fragment" => Fragments.Fragment Symbol\n','local notation "Fragment" => Fragments.Fragment Symbol\nlocal notation "Heap" => SourceEqualityAnnotationHeap.Heap\n')
text=text.replace('variable {width : Nat}','variable {bits : Nat}').replace('Caller width','Caller (bits + 2)')
text=text.replace('theorem stable_complete_neutral_sound_current\n','theorem stable_complete_neutral_sound_current_resources\n    (seed : Seed)\n')
text=text.replace('    (ranges : Ranges checkEmpty scs edge caller before memos.query)\n','    (fits : Fits seed.2 caller.checked)\n    (reserved : Reserved bits seed (cost edge scs before.core.counter tries))\n    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)\n')
text=text.replace('    stable_complete_neutral_semantics formulas solver','    stable_complete_neutral_semantics_resources seed formulas solver')
text=text.replace('bounded pending allowed tries residual projected ranges observed','bounded pending allowed tries residual projected fits reserved known observed')
assert 'ranges' not in text
(out/'SourcePruningEnumerationSelectedEdgeNeutralResourceSoundness.lean').write_text(text)
import hashlib
for p in sorted(out.glob('*.lean')):print(p,len(p.read_bytes().splitlines()),len(p.read_bytes()),hashlib.sha256(p.read_bytes()).hexdigest())
