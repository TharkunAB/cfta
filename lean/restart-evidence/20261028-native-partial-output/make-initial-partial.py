from pathlib import Path
import hashlib,json
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
area=Path('/tmp/mcfta-native-partial-output-20261028')
old=(root/'SourcePruningEnumerationInitialRenderCarriers.lean').read_text()
head=old[:old.index('/-- Original startup')]
head=head.replace('import MicroCFTA.SourcePruningEnumerationResourceHistoryProper',
 'import MicroCFTA.SourcePruningEnumerationResourceHistoryProper\nimport MicroCFTA.SourcePruningEnumerationHistoryPartialOutput')
start=head.index('/-!');end=head.index('-/',start)+2
head=head[:start]+'''/-!
# Native partial output for every actual output from original startup

The complete old startup and concrete-render contract remains first.
The same actual resource history constructs a partial root observation.
Its bound, partial term, full state and packet precede every semantic model.
-/'''+head[end:]
old_name='run_initial_finite_render_sound_carriers'
new_name='run_initial_finite_render_sound_partial'
old_decl=old[old.index('theorem '+old_name):].split(':= by',1)[0].rstrip()
declaration=old_decl.replace('theorem '+old_name,'theorem '+new_name,1)
start=declaration.index('      (((∀ extra,')+6
declaration=declaration[:start]+'('+declaration[start:]
history=(root/'SourcePruningEnumerationHistoryPartialOutput.lean').read_text()
observer=history[history.index('    ∃ (finalInventory'):history.index(' := by')].rstrip()
declaration+=') ∧\n      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,\n'+observer
cut=declaration[:declaration.rfind(') ∧\n      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,')]
recovered=(cut[:start]+cut[start+1:]).replace('theorem '+new_name,'theorem '+old_name,1)
assert recovered==old_decl
proof=''' := by
  obtain ⟨handle, encoded, decoded, bound, outcome, retained⟩ :=
    run_initial_finite_render_sound_carriers holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos metadata value seed ceiling context available
      closed emptyPending bounded known selectionMembers selectionLength reserved arity
  refine ⟨handle, encoded, decoded, bound, outcome, retained, ?_⟩
  have initialReferences : EnumerationGraphReferences.ReferencesCarry (EnumerationState.initial handle : Core) :=
    EnumerationRenderability.initial_references handle
  have rootCarrier : EnumerationCarriers.CarriesGraph (EnumerationState.initial handle : Core) 0 :=
    EnumerationCarriers.carries_self (EnumerationState.initial handle) (initial_storage handle).total
      0 (.unenumerated (some handle) []) rfl trivial
  intro output member
  have history := retained.1.1.2.2.1 0 output member
  exact history.root_partial_complete_models initialReferences rootCarrier

end MicroCFTA.SourcePruningEnumerationRecursive
'''
name='SourcePruningEnumerationInitialPartialOutput.lean'
data=head+'/-- Retain the full original startup contract and construct partial output at every emitted cache. -/\n'+declaration+proof
(root/name).write_text(data)
draft=area/'root-drafts/v5-history-partial-output';draft.mkdir()
for name in ['SourcePruningEnumerationHistoryPartialOutput','SourcePruningEnumerationInitialPartialOutput']:
 (draft/(name+'.lean')).write_bytes((root/(name+'.lean')).read_bytes())
(draft/'old-initial-carrier-declaration.txt').write_text(old_decl)
(draft/'recovered-initial-carrier-declaration.txt').write_text(recovered)
(draft/'contract-comparison.json').write_text(json.dumps(dict(status='pass',bytes=len(old_decl.encode()),sha256=hashlib.sha256(old_decl.encode()).hexdigest(),entire_original_declaration=True,new_input_admission=False,original_producer_calls=1),indent=2)+'\n')
print('Old startup declaration retained:',len(old_decl.encode()),'bytes')
