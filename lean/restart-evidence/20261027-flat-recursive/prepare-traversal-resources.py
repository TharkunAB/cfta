from pathlib import Path
r=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
old=(r/'SourcePruningEnumerationTraversalResources.lean').read_text()
flat=(r/'SourceFlatPruningTraversalCompletion.lean').read_text()
start=old.index('theorem complete_with_fragments_resources\n'); sep=old.index(' := by\n',start);end=old.index('\n/-- Original resources retain the full earlier traversal interface.',sep)
header=old[:sep]
header=header.replace('import MicroCFTA.SourcePruningEnumerationTraversalCompletion\nimport MicroCFTA.SourcePruningEnumerationChildResources','import MicroCFTA.SourcePruningEnumerationTraversalResources\nimport MicroCFTA.SourceFlatPruningChildResources\nimport MicroCFTA.SourceFlatPruningChildTraversal')
header=header.replace('namespace MicroCFTA.SourcePruningEnumerationTraversalCompletion','namespace MicroCFTA.SourceFlatPruningTraversalResources')
header=header.replace('# Original resource completion for successive children','# Actual flat traversal from original child resources')
coststart=header.index('/-- Each original child bucket reserves');costend=header.index('/-- Original resources retain the full traversal packet')
helperstart=flat.index('/-- A related successful singleton');helperend=flat.index('/-- Original admission derives the full earlier packet')
header=header[:coststart]+'open SourcePruningEnumerationTraversalCompletion (cost)\n\n'+flat[helperstart:helperend]+header[costend:]
fam=flat[flat.index('      (∀ (flat : EnumerationFlatCached.Cached'):flat.index(' := by\n',flat.index('      (∀ (flat : EnumerationFlatCached.Cached'))].replace('Result width','Result (bits + 2)')
body=old[sep:end]
def replace(a,b):
 global body
 assert body.count(a)==1,(a,body.count(a))
 body=body.replace(a,b)
replace('.inl ⟨rfl, safe, by simp⟩, fits, known⟩','.inl ⟨rfl, safe, by simp⟩, fits, known, ?_⟩')
nilflat=flat[flat.index('      · intro flat related _extraNative'):flat.index('  | cons input rest ih =>')]
replace('  | cons input rest ih =>',nilflat+'  | cons input rest ih =>')
replace('headReferences, headPending, shape, middleFits, middleKnown⟩ :=','headReferences, headPending, shape, middleFits, middleKnown, headFlat⟩ :=')
replace('SourcePruningEnumerationChildCompletion.complete_with_fragments_resources seed','SourceFlatPruningChildResources.complete_with_fragments_resources seed')
replace('.inr ⟨outer, waiting, rfl⟩, ?_, ?_⟩','.inr ⟨outer, waiting, rfl⟩, ?_, ?_, ?_⟩')
rejectflat=flat[flat.index('        · intro flat related en P H largeP largeH'):flat.index('      · have tailGenuine')].replace('Result width','Result (bits + 2)')
replace('      · have tailGenuine',rejectflat+'      · have tailGenuine')
replace('tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown⟩ :=','tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown, tailFlat⟩ :=')
replace('?_, ?_, finalFits, finalKnown⟩','?_, ?_, finalFits, finalKnown, ?_⟩')
tailstart=flat.index('        · intro flat related en P H largeP largeH',flat.index('        · intro flat related en P H largeP largeH')+1)
tailflat=flat[tailstart:flat.index('\nend MicroCFTA.SourceFlatPruningTraversalCompletion')].replace('Result width','Result (bits + 2)')
source=header+' ∧\n'+fam+body+'\n'+tailflat+'\n\nend MicroCFTA.SourceFlatPruningTraversalResources\n'
p=r/'SourceFlatPruningTraversalResources.lean';assert not p.exists();p.write_text(source)
print('Prepared actual traversal resource induction.')
