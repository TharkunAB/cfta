from pathlib import Path
r=Path('/home/tritlo/Code/mcfta');a=Path('/tmp/mcfta-history-boundary-exclusion-20261027');old=(r/'lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryCanonical.lean').read_text()
start=old.index('theorem run_finite_complete_resources_canonical');end=old.index(' := by',start);header=old[start:end]
prefix=old[:old.index('/-- The complete original producer')]
prefix=prefix.replace('import MicroCFTA.SourcePruningEnumerationResourceHistoryCanonical','import MicroCFTA.SourcePruningEnumerationHistoryRenderingSoundness\nimport MicroCFTA.SourcePruningEnumerationFiniteHistoryCanonical').replace('open EnumerationState EnumerationValidity InternedConstructorTemplates','open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates\nopen SourcePruningEnumerationNodes').replace('local notation "Node" => Value Symbol Constraint','local notation "Node" => Value Symbol Constraint\nlocal notation "Core" => EnumerationState.State Symbol Constraint')
observer='''
      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output →
        ∀ (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (fuel uv : Nat)
          (after : Core) (term : Language.Term Symbol) (pending : List (Constraint × Language.Term Symbol))
          (handle : Nat) (bucket : List Suspended) (value : Node),
        SourcePruningEnumerationRendering.Discharged output.cache.core →
        Success (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker fuel uv)
          output.cache.core (term, pending) after →
        (∀ obligation ∈ pending, SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) →
        before.core.values[uv]? = some (.unenumerated (some handle) bucket) →
        lookupNode caller.checked.native.machine.heap handle = some value →
        ∃ assignment : Nat → Language.Term Symbol,
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment before.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ∧
          (∀ sc ∈ bucket, Suspended.Holds assignment term sc) ∧ term = assignment uv ∧
          EnumerationCompressionFrame.Frame output.cache.core after ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient output.caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment output.cache.core ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient output.caller.checked.native.machine.heap)
            (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
            assignment after'''
needle='      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome, Canonical output.cache.core'
assert header.count(needle)==1
newheader=header.replace('theorem run_finite_complete_resources_canonical','theorem run_finite_complete_resources_render_sound').replace(needle,'      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome, Canonical output.cache.core) ∧'+observer)
proof=''' := by
  obtain ⟨bound, outcome, running, resources, histories, outputCanonical⟩ :=
    run_finite_complete_resources_canonical holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved canonical
  refine ⟨bound, outcome, running, resources, histories, outputCanonical, ?_⟩
  intro extra output _member history ambient marker fuel uv after term pending handle bucket value
    discharged observed checked stored decoded
  exact history.render_sound rfl canonical discharged ambient marker fuel uv after term pending observed checked
    handle bucket value stored decoded

end MicroCFTA.SourcePruningEnumerationRecursive
'''
folder=a/'root-drafts/v1';(folder/'SourcePruningEnumerationFiniteHistoryRendering.lean').write_text(prefix+'/-- Retain the full finite producer result and check rendered original acceptance for arity-certified histories. -/\n'+newheader+proof)
contracts=a/'root-contracts';contracts.mkdir();(contracts/'finite-canonical-original-header.txt').write_text(header);(contracts/'finite-rendering-full-header.txt').write_text(newheader)
recovered=newheader.replace('theorem run_finite_complete_resources_render_sound','theorem run_finite_complete_resources_canonical').replace('      (∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome, Canonical output.cache.core) ∧'+observer,needle)
assert recovered==header;(contracts/'finite-canonical-recovered-header.txt').write_text(recovered)
print('Drafted full-contract finite producer observer; old header recovers byte-exact.')
