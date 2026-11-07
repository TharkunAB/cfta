import MicroCFTA.SourceSizedDeterminizationSourceOutput

/-!
# Signed internal determinization limits

The source helper accepts an `Int`. A negative limit rejects even an
empty known set. Conversion to a natural limit must follow that check.
The public Sized path uses the positive constant 1024.

This wrapper specifies returned values. It does not count initial batch
work or prove native machine-integer and container-size correspondence.
Signed query sizes and ranks have a separate exact API contract.
-/
namespace MicroCFTA.SourceSizedDeterminizationSignedLimit
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationClosure
open SourceSizedDeterminizationDiscovery Std
attribute [local instance] lexOrd

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
  [Ord State] [Ord Symbol]

/-- Reject negative internal limits before converting the limit to a natural number. -/
def compile (limit : Int) (states : List State) (rows : Automaton State Symbol) :
    Outcome (List State) (List (Choice State Symbol)) :=
  if limit < 0 then .limitExceeded
  else SourceSizedDeterminizationSourceLoop.compile limit.toNat states rows

/-- Every mathematical set cardinality exceeds a negative internal limit. -/
theorem negative_guard (limit : Int) (count : Nat) (negative : limit < 0) :
    limit < (count : Int) := by omega

/-- Negative internal limits reject all source inputs, including empty inputs. -/
theorem negative_rejected (limit : Int) (states : List State) (rows : Automaton State Symbol)
    (negative : limit < 0) : compile limit states rows = .limitExceeded := by
  rw [compile, ite_eq_left negative]

/-- Nonnegative internal limits use the complete natural controller. -/
theorem nonnegative (limit : Int) (states : List State) (rows : Automaton State Symbol)
    (valid : 0 ≤ limit) :
    compile limit states rows = SourceSizedDeterminizationSourceLoop.compile limit.toNat states rows := by
  rw [compile, ite_eq_right (by omega)]

/-- Natural limits retain exactly the source set and holder execution. -/
theorem natural (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    compile (limit : Int) states rows = SourceSizedDeterminizationSourceLoop.compile limit states rows := by
  rw [nonnegative _ _ _ (by omega), Int.toNat_natCast]

/-- The actual public 1024-key path uses the proved natural source controller. -/
theorem sized (states : List State) (rows : Automaton State Symbol) :
    compile 1024 states rows = SourceSizedDeterminizationSourceLoop.compile 1024 states rows :=
  natural 1024 states rows

variable [TransOrd State] [LawfulEqOrd State]

/-- No signed internal call exhausts its computed recursion bound. -/
theorem terminal (limit : Int) (states : List State) (rows : Automaton State Symbol) :
    compile limit states rows ≠ .exhausted := by
  by_cases negative : limit < 0
  · rw [negative_rejected limit states rows negative]
    intro impossible
    cases impossible
  · rw [nonnegative limit states rows (by omega)]
    exact SourceSizedDeterminizationSourceLoop.compile_terminal limit.toNat states rows

omit [TransOrd State] [LawfulEqOrd State] in
/-- A returned signed call derives its nonnegative limit and natural execution. -/
theorem ready_natural (limit : Int) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) :
    0 ≤ limit ∧ SourceSizedDeterminizationSourceLoop.compile limit.toNat states rows = .ready known choices := by
  have valid : 0 ≤ limit := by
    by_cases negative : limit < 0
    · rw [negative_rejected limit states rows negative] at returned
      cases returned
    · omega
  exact ⟨valid, (nonnegative limit states rows valid).symm.trans returned⟩

/-- Returned signed calls derive their complete row closure without a caller invariant. -/
theorem ready_closed (limit : Int) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) : Closed states rows known choices :=
  SourceSizedDeterminizationSourceLoop.compile_closed limit.toNat states rows known choices
    (ready_natural limit states rows known choices returned).2

variable [Ord (Sum State (List State))]

/-- Signed internal success gives the exact canonical signed query contract. -/
theorem queries_exact (limit : Int) (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows) (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (root : State) (present : root ∈ states) :
    SourceSizedApiLaws.Exact
      (SourceSizedDispatcher.optimizedApi
        (SourceSizedDecided.automaton
          (SourceSizedDeterminizationSourceOutput.sortedRows limit.toNat states rows known choices
            (ready_natural limit states rows known choices returned).2 root present) (fun _ _ => true))
        (.inl root)) (Accepts rows root) :=
  SourceSizedDeterminizationSourceOutput.queries_exact limit.toNat states rows plain supported known choices
    (ready_natural limit states rows known choices returned).2 root present

end MicroCFTA.SourceSizedDeterminizationSignedLimit
