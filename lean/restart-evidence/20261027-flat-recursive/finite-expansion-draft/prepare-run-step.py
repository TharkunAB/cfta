from pathlib import Path
import re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
area=Path('/tmp/mcfta-flat-recursive-20261027/finite-expansion-draft')
s=(root/'SourcePruningEnumerationFiniteRunStep.lean').read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationFiniteExpansionResources','import MicroCFTA.SourceFlatPruningRecursiveExpansionResources')
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationRecursive','namespace MicroCFTA.SourceFlatPruningRecursive').replace('end MicroCFTA.SourcePruningEnumerationRecursive','end MicroCFTA.SourceFlatPruningRecursive')
s=s.replace('open EnumerationState InternedConstructorTemplates','open EnumerationState InternedConstructorTemplates\nopen SourcePruningEnumerationRecursive (Packet OutcomeResources resume_zero_outcome_resources)')
# The original driver remains the first member of the retained packet.
s=re.sub(r'(?<![A-Za-z0-9_.])run\b','SourcePruningEnumerationRecursive.run',s)
s=re.sub(r'(?<![A-Za-z0-9_.])resume\b','SourcePruningEnumerationRecursive.resume',s)
s=s.replace('        (SourcePruningEnumerationFiniteReservation.final (recursiveFuel + 1) seed ceiling) outcome := by','''        (SourcePruningEnumerationFiniteReservation.final (recursiveFuel + 1) seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          run holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) (recursiveFuel + 1) metadata caller memos.query flat = flatOutcome ∧
          ResultRelated flatOutcome outcome := by''')
s=s.replace('⟨bound, outcome, running, resources⟩ := selected_finite_complete_resources','⟨bound, outcome, running, resources, flatRunning⟩ := selected_finite_complete_resources')
old='''    exact ⟨bound, outcome, fun extra => by simpa only [SourcePruningEnumerationRecursive.run, chosen] using running extra, resources⟩'''
new='''    refine ⟨bound, outcome, fun extra => by simpa only [SourcePruningEnumerationRecursive.run, chosen] using running extra,
      resources, ?_⟩
    intro flat related extra
    obtain ⟨flatOutcome, actual, corresponds⟩ := flatRunning flat related extra
    refine ⟨flatOutcome, ?_, corresponds⟩
    unfold run
    rw [SourceFlatPruningRestart.decision_related related stop order metadata, chosen]
    exact actual'''
assert old in s
s=s.replace(old,new)
start=s.index('    refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩')
s=s[:start]+'''    have originalRunning : ∀ extra,
        SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf stop order
          (0 + extra) (recursiveFuel + 1) metadata caller memos.query before = outcome := by
      intro extra
      have zero := running extra
      unfold SourcePruningEnumerationRecursive.run
      cases selected : SourcePruningEnumerationRestart.decision stop order metadata before with
      | none => simpa only [selected, SourcePruningEnumerationRecursive.resume, Nat.zero_add] using zero
      | some next =>
          cases next with
          | done => simpa only [selected, SourcePruningEnumerationRecursive.resume, Nat.zero_add] using zero
          | stuck => simpa only [selected, SourcePruningEnumerationRecursive.resume, Nat.zero_add] using zero
          | expand uv => exact False.elim (expansion ⟨uv, selected⟩)
    refine ⟨0, outcome, originalRunning, resources.mono growth.1 growth.2, ?_⟩
    intro flat related extra
    refine ⟨_, rfl, ?_⟩
    rw [← originalRunning extra]
    unfold run SourcePruningEnumerationRecursive.run
    rw [SourceFlatPruningRestart.decision_related related stop order metadata]
    apply resume_nonexpanding_related holeKey fits admits graph templates checkEmpty edgesOf stop order
      (0 + extra) metadata caller memos.query flat before related (recursiveFuel + 1)
      (SourcePruningEnumerationRestart.decision stop order metadata before)
    intro uv chosen
    exact expansion ⟨uv, chosen⟩

end MicroCFTA.SourceFlatPruningRecursive
'''
s=s.replace('# The actual recursive driver at positive finite depth','# Actual flat and original drivers at positive finite depth')
(area/'SourceFlatPruningRecursiveRunStep.lean').write_text(s)
s=(root/'SourcePruningEnumerationFiniteResources.lean').read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationFiniteRunStep','import MicroCFTA.SourceFlatPruningRecursiveRunStep')
s=s.replace('namespace MicroCFTA.SourcePruningEnumerationRecursive','namespace MicroCFTA.SourceFlatPruningRecursive').replace('end MicroCFTA.SourcePruningEnumerationRecursive','end MicroCFTA.SourceFlatPruningRecursive')
s=s.replace('open EnumerationState InternedConstructorTemplates','open EnumerationState InternedConstructorTemplates\nopen SourcePruningEnumerationRecursive (Packet OutcomeResources)')
zero=s.index('  | zero =>')
succ=s.index('  | succ recursiveFuel ih =>',zero)
s=s[:zero]+'''  | zero =>
      exact zero_complete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
'''+s[succ:]
s=s.replace('      (∀ extra, run holeKey','      (∀ extra, SourcePruningEnumerationRecursive.run holeKey')
s=s.replace('        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome :=','''        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          run holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel metadata caller memos.query flat = flatOutcome ∧
          ResultRelated flatOutcome outcome :=''')
s=s.replace('# Original resources for every finite recursive capacity','# Actual flat correspondence at every finite recursive capacity')
s=s.replace('The zero case uses\nthe exact original decision.','The zero case uses\nthe exact original decision. Every related flat input follows the same stable old result.')
(area/'SourceFlatPruningRecursiveFiniteResources.lean').write_text(s)
