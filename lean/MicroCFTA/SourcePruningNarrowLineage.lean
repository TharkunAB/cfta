import MicroCFTA.SourcePruningNarrowControl

/-!
# Strict row loss for changed ordinary narrowing handles

A physical ordinary normal form keeps its identity when a filter keeps all
of its root rows. A changed encoded handle therefore loses a complete row.
The row source remains fixed for this step. Other writers need separate bounds.

-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Key : Type}

/-- A changed normal ordinary handle strictly loses a complete root row. -/
theorem narrowAt_changed_loses_row [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (oldHandle newHandle : Nat)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (normal : EqualityOrdinaryReadback.Normal before value)
    (returned : narrowAt fits admits fuel key value before = .done result after)
    (oldEncoded : SourcePruningEnumerationNodes.encodeNode value = some oldHandle)
    (newEncoded : SourcePruningEnumerationNodes.encodeNode result = some newHandle)
    (changed : newHandle ≠ oldHandle) :
    (∀ edge ∈ nodeEdges result, edge ∈ nodeEdges value) ∧
      ∃ edge ∈ nodeEdges value, edge ∉ nodeEdges result := by
  classical
  have rows := narrowAt_ordinary_rows fits admits fuel key value result before after ready available ordinary returned
  refine ⟨fun edge member => (rows edge member).1, ?_⟩
  apply Classical.byContradiction
  intro noLoss
  have allKept : ∀ edge ∈ nodeEdges value, keeps fits admits key edge = true := by
    intro edge member
    have retained : edge ∈ nodeEdges result := by
      apply Classical.byContradiction
      intro absent
      exact noLoss ⟨edge, member, absent⟩
    exact (rows edge retained).2
  have replay := narrowAt_of_normal fits admits fuel key value before ordinary normal allKept
  rw [replay] at returned
  have same := MergedSourceComparison.Result.done.inj returned
  rw [← same.1] at newEncoded
  exact changed (Option.some.inj (newEncoded.symm.trans oldEncoded))

/-- An actual earlier constructor and its cache lineage supply the current normal input. -/
theorem narrowAt_constructed_changed_loses_row [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (edges : List (EdgeValue Symbol Guard))
    (value result : Value Symbol Guard) (original built before after : State Symbol Guard)
    (oldHandle newHandle : Nat)
    (ready : SourceEqualityRequiredCache.Ready original)
    (resident : InternedNestedProvenance.Edges original edges)
    (closed : MergedColdReaderClosedInputs.ClosedEdges edges)
    (constructed : run (makeNode edges) original = (value, built))
    (lineage : SourceEqualityRequiredCache.Keeps built before)
    (returned : narrowAt fits admits fuel key value before = .done result after)
    (oldEncoded : SourcePruningEnumerationNodes.encodeNode value = some oldHandle)
    (newEncoded : SourcePruningEnumerationNodes.encodeNode result = some newHandle)
    (changed : newHandle ≠ oldHandle) :
    (∀ edge ∈ nodeEdges result, edge ∈ nodeEdges value) ∧
      ∃ edge ∈ nodeEdges value, edge ∉ nodeEdges result := by
  have builtFacts := SourceEqualityRequiredCache.node edges original ready resident closed
  simp only [constructed] at builtFacts
  have builtNormal : EqualityOrdinaryReadback.Normal built value := by
    have result := EqualityOrdinaryReadback.makeNode_normal edges original built
      ready.semantic.1.normal.facts.coherent ready.semantic.1.normal.facts.linked
      builtFacts.1.ready.semantic.1.normal.facts.coherent resident
      (by simpa only [constructed] using grows_refl built)
    simpa only [constructed] using result
  have beforeNormal := EqualityOrdinaryReadback.normal_grows built before
    builtFacts.1.ready.semantic.1.normal.facts.coherent.valid lineage.growth value builtNormal
  exact narrowAt_changed_loses_row fits admits fuel key value result before after oldHandle newHandle
    lineage.ready (lineage.available value builtFacts.2.1) builtFacts.2.2.2 beforeNormal
    returned oldEncoded newEncoded changed

end MicroCFTA.SourcePruningNativeView
