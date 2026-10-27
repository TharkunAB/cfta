from pathlib import Path
import difflib,hashlib,json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryRendering.lean').read_text()
start=old.index('theorem run_finite_complete_resources_render_sound\n');end=old.index(' := by',start)
header=old[start:end]
newname='run_finite_complete_resources_render_sound_from_initial_arity'
arity='    (arity : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap)'
gate='''        ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output →
'''
assert header.count(gate)==1
newheader=header.replace('theorem run_finite_complete_resources_render_sound\n','theorem '+newname+'\n',1).replace('    (canonical : Canonical before.core) :','    (canonical : Canonical before.core)\n'+arity+' :',1).replace(gate,'',1)
recovered=newheader.replace('theorem '+newname+'\n','theorem run_finite_complete_resources_render_sound\n',1).replace('    (canonical : Canonical before.core)\n'+arity+' :','    (canonical : Canonical before.core) :',1)
marker='''      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
''';assert recovered.count(marker)==1;recovered=recovered.replace(marker,marker+gate,1);assert recovered==header
prelude=old[:start];a=prelude.index('/-!');b=prelude.index('-/',a)+2
prelude=prelude[:a]+'''/-!
# Finite checked rendering from genuine initial arity

The original finite resource admission derives every actual arity history.
The same output's checked native rendering implies original acceptance.
No supplied arity history or desired final satisfaction is an input.
-/'''+prelude[b:]
prelude='import MicroCFTA.SourcePruningEnumerationFiniteHistoryResourcesArity\n'+prelude
prelude=prelude.replace('/-- Retain the full finite producer result and check rendered original acceptance for arity-certified histories. -/','/-- Original finite resources and genuine initial arity derive checked rendered acceptance at each own output. -/')
body=''' := by
  obtain ⟨bound, outcome, running, resources, histories, _arityResources, arityHistories⟩ :=
    run_finite_complete_resources_with_history_arity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved arity
  have outputCanonical : ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
      Canonical output.cache.core := by
    intro output member
    exact (histories 0 output member).canonical_output canonical
  refine ⟨bound, outcome, running, resources, histories, outputCanonical, ?_⟩
  intro extra output member ambient marker fuel uv after term pending handle bucket value
    discharged observed checked stored decoded
  exact (arityHistories extra output member).render_sound rfl canonical discharged ambient marker fuel uv
    after term pending observed checked handle bucket value stored decoded

end MicroCFTA.SourcePruningEnumerationRecursive
'''
folder=area/'render-consumer/drafts/v1';folder.mkdir(parents=True);p=folder/'SourcePruningEnumerationFiniteHistoryRenderingArity.lean';p.write_text(prelude+newheader+body)
records={'old':header,'new':newheader,'recovered':recovered,'identical':header==recovered,'removed_observer_antecedent':gate,'new_last_admission':arity,'scope':'All original producer admissions/results preserved; the observer no longer takes a supplied arity-certified history. Initial genuine arity Heap is last input. No desired acceptance or final Satisfies input.'}
(area/'render-consumer/contract-comparison.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps({'source':str(p),'lines':len(p.read_text().splitlines()),'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'full_header_recovery':True}))
