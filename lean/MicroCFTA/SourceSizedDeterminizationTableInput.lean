import MicroCFTA.SourceSizedDeterminizationSignedLimit
import MicroCFTA.SourceSizedDeterminizationTargetReadback

/-!
# Determinization from the original explicit table

The source determinizes all erased original rows. It does not restrict
that shared table to the states reached from one root. Original map keys
supply the owner list. Erased rows supply plain guards and owner support.

Successful current structural validation supplies root membership. A
returned signed compilation then supplies the exact canonical query API
for the erased original language. Scoped guard erasure and the complete
Sized dispatch remain separate. No original-input resource bound is proved.
-/
namespace MicroCFTA.SourceSizedDeterminizationTableInput
open Language SourceSizedFiniteKeys SourceSizedDecided Std
open SourceSizedDeterminizationKernel SourceSizedDeterminizationDiscovery
attribute [local instance] lexOrd

variable {State Symbol Payload : Type} [DecidableEq State]

/-- Erase constraints on every original row without changing transition order. -/
def rows (table : Table State Symbol Payload) : Automaton State Symbol :=
  automaton (SourceSizedFiniteKeys.lookup table) (fun _ _ => true)

/-- Every erased original row has a true guard. -/
theorem rows_plain (table : Table State Symbol Payload) : Decoder.Plain (rows table) := by
  intro state edge member term
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp member
  rfl

variable [Ord State]

/-- The actual original map keys are ascending under the source comparison. -/
theorem keys_ordered [TransOrd State] (table : Table State Symbol Payload) :
    (SourceDenseRows.keys table).Pairwise
      (fun first second => (compare first second).isLE = true) :=
  CanonicalClasses.sortedSet_ordered (table.map Prod.fst)

/-- Every erased transition owner belongs to the original map's finite key list. -/
theorem rows_supported (table : Table State Symbol Payload) (state : State)
    (edge : Edge State Symbol) (member : edge ∈ rows table state) :
    state ∈ SourceDenseRows.keys table := by
  obtain ⟨raw, stored, _⟩ := List.mem_map.mp member
  unfold SourceSizedFiniteKeys.lookup at stored
  obtain ⟨entry, present, found⟩ := List.mem_flatMap.mp stored
  by_cases same : entry.1 = state
  · exact (SourceDenseRows.mem_keys table state).mpr (List.mem_map.mpr ⟨entry, present, same⟩)
  · simp only [ite_eq_right same, List.not_mem_nil] at found

variable [DecidableEq Symbol]

/-- Original map keys give literal source target equality at the token's arity. -/
theorem source_target_readback [TransOrd State] [LawfulEqOrd State]
    (table : Table State Symbol Payload) (wanted : Symbol × Nat)
    (keys : List (List State)) (arity : keys.length = wanted.2) :
    SourceSizedDeterminizationZipTarget.sourceTarget (SourceDenseRows.keys table) (rows table) wanted keys =
      target (SourceDenseRows.keys table) (rows table) wanted.1 keys :=
  SourceSizedDeterminizationTargetReadback.sourceTarget_readback
    (SourceDenseRows.keys table) (rows table) wanted keys arity
    (SourceDenseRows.keys_nodup table) (keys_ordered table)

/-- Every tuple generated from the original table has its literal source target. -/
theorem generated_source_target_eq [TransOrd State] [LawfulEqOrd State]
    (table : Table State Symbol Payload)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) (keys : List (List State))
    (member : keys ∈ SourceSizedDeterminizationOrderedStep.tupleSet
      (SourceDenseRows.keys table) (rows table) fresh holding known wanted) :
    SourceSizedDeterminizationZipTarget.sourceTarget (SourceDenseRows.keys table) (rows table) wanted keys =
      target (SourceDenseRows.keys table) (rows table) wanted.1 keys :=
  SourceSizedDeterminizationTargetReadback.generated_source_target_eq
    (SourceDenseRows.keys table) (rows table) (SourceDenseRows.keys_nodup table) (keys_ordered table)
    fresh holding known wanted keys member

variable [Ord Symbol]

/-- Run signed bounded discovery on all erased original rows and actual original map keys. -/
def compile (limit : Int) (table : Table State Symbol Payload) :
    Outcome (List State) (List (Choice State Symbol)) :=
  SourceSizedDeterminizationSignedLimit.compile limit (SourceDenseRows.keys table) (rows table)

/-- Original-table compilation never exhausts its computed recursion bound. -/
theorem compile_terminal [TransOrd State] [LawfulEqOrd State]
    (limit : Int) (table : Table State Symbol Payload) : compile limit table ≠ .exhausted :=
  SourceSizedDeterminizationSignedLimit.terminal limit (SourceDenseRows.keys table) (rows table)

variable [TransOrd State] [LawfulEqOrd State] [Ord (Sum State (List State))]

/-- Compute canonical output rows from the returned source run and the validated original root. -/
def sortedRows (limit : Int) (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit table = .ready known choices) :=
  SourceSizedDeterminizationSourceOutput.sortedRows limit.toNat (SourceDenseRows.keys table) (rows table)
    known choices
    (SourceSizedDeterminizationSignedLimit.ready_natural
      limit (SourceDenseRows.keys table) (rows table) known choices returned).2
    root (SourceSizedStructuralKeys.validated_root table root success)

/-- Original validation and actual source success give every exact signed query law. -/
theorem queries_exact (limit : Int) (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit table = .ready known choices) :
    SourceSizedApiLaws.Exact
      (SourceSizedDispatcher.optimizedApi
        (automaton (sortedRows limit table root success known choices returned) (fun _ _ => true))
        (.inl root)) (Accepts (rows table) root) :=
  SourceSizedDeterminizationSignedLimit.queries_exact limit (SourceDenseRows.keys table) (rows table)
    (rows_plain table) (rows_supported table) known choices returned root
    (SourceSizedStructuralKeys.validated_root table root success)

end MicroCFTA.SourceSizedDeterminizationTableInput
