from pathlib import Path
import re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
a=(root/'SourcePruningEnumerationPrefixCheckpointModels.lean').read_text();b=(root/'SourcePruningEnumerationPreparedEntryModels.lean').read_text()
header=a[a.index('namespace MicroCFTA.SourcePruningEnumerationRecursive'):a.index('/-- Keep every')]
header=header.replace('namespace MicroCFTA.SourcePruningEnumerationRecursive','namespace MicroCFTA.SourcePruningEnumerationPreparedEntryModels\nopen SourcePruningEnumerationRecursive (Packet)')
header=header.replace('open SourcePruningEnumerationSelectedStep (PrefixValid Resources runPrefix)','open SourcePruningEnumerationSelectedStep (PrefixValid Resources runPrefix)\nopen InternedProbeProvenance\nopen SourcePruningEnumerationNodes (lookupNode)\nopen SourceCurrentConstrainedCapEditForecast (headProfile)\nlocal notation "Core" => EnumerationState.State Symbol Constraint')
# Core notation must follow its two constituent notations.
header=header.replace('local notation "Core" => EnumerationState.State Symbol Constraint\n','')
header=header.replace('local notation "Node" => Value Symbol Constraint','local notation "Node" => Value Symbol Constraint\nlocal notation "Core" => EnumerationState.State Symbol Constraint')
sig=a[a.index('theorem packet_prefix_complete_resources_models'):a.index(' := by')].replace('theorem packet_prefix_complete_resources_models','theorem packet_prefix_preparation_complete_models')
point=sig.index('      (PrefixValid')
sig=sig[:point]+'      ('+sig[point:].lstrip() + ') ∧\n'
result=b[b.index('    match observed with'):b.index(' := by')]
result=re.sub(r'\buv\b','selected',result)
sig+=result
body=''' := by
  obtain ⟨bound, complete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete_resources_models
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before packet profile property bounded known
  refine ⟨bound, ?_⟩
  intro extra selected chosen
  have retained := complete extra selected chosen
  refine ⟨retained, ?_⟩
  exact narrowed_preparation_complete_models holeKey fits admits graph templates checkEmpty edgesOf stop order
    metadata formulas solver inventory (bound + extra) selected caller memos before packet chosen
    profile property bounded known _ rfl retained.1.1

end MicroCFTA.SourcePruningEnumerationPreparedEntryModels
'''
(root/'SourcePruningEnumerationPreparedPrefixModels.lean').write_text('''import MicroCFTA.SourcePruningEnumerationPreparedEntryModels

/-!
# Original-input model transport to actual prepared branch entry

One original packet fixes a common selected-prefix work bound.
Each actual retained narrowing cache derives one native preparation.
Every earlier prefix, admission and preparation field remains available.
The same original accepted assignment reaches the prepared branch entry.
The statement supplies no future successful receipt or semantic model.
-/
'''+header+'/-- Original inputs derive the full selected-prefix and native-preparation model path. -/\n'+sig+body)
