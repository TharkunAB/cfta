import MicroCFTA.SourcePruningOracleRefutation
import MicroCFTA.SourcePruningRecordTypes

/-!
# Original assignment refutation through type recording

The metadata wrapper retains the actual template oracle result.
An empty template catalog retains the original pending groups.
-/
namespace MicroCFTA.SourcePruningRecordTypes
open Language Fragments EnumerationState EnumerationCorrectness
open SourcePruningPartialMatch SourcePruningTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Typing : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Actual type recording keeps an original assignment that refutes every forbidden match. -/
theorem recordTypes_inl_refutes (graph : Graph Symbol Guard)
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (templates : List (Template.Pattern Symbol))
    (fuel uv : Nat) (metadata : Metadata Typing) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (result : Bool × Metadata Typing)
    (total : UnionFind.Total before.representatives)
    (satisfied : Satisfies language meaning assignment before)
    (filled : fill assignment fragment = assignment uv)
    (refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group)
    (avoids : Avoids templates (fill assignment fragment))
    (encoded : ∀ program, ProgramAt (fill assignment fragment) program → ProgramEncoding program)
    (success : Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before result after) :
    result.1 = false ∧ ∀ group ∈ result.2.pending, SourcePruningResume.Refutes assignment group := by
  cases templates with
  | nil =>
      rw [recordTypes_empty] at success
      obtain ⟨rfl, _same⟩ := (success_pure _ result before after).mp success
      exact ⟨rfl, refuted⟩
  | cons first rest =>
      change Success (SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv (.inl fragment) >>=
        fun observed => pure (observed.1, {metadata with pending := observed.2,
          types := updatedTypes metadata uv (.inl fragment)})) before result after at success
      obtain ⟨observed, middle, checked, final⟩ := (success_bind _ _ _ _ _).mp success
      have retained := SourcePruningOracle.oracle_inl_refutes graph language meaning assignment
        (first :: rest) fuel uv metadata.pending fragment before middle observed total satisfied
        filled refuted avoids encoded checked
      obtain ⟨rfl, _same⟩ := (success_pure _ result middle after).mp final
      exact retained

end MicroCFTA.SourcePruningRecordTypes
