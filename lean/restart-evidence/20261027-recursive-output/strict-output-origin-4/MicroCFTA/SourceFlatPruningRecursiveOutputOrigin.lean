import MicroCFTA.SourceFlatPruningOutputFlow
import MicroCFTA.SourceFlatPruningOutputFrontier

/-!
# The actual frontier of each flat recursive output

Every emitted output retains its own cache, caller and query table.
Its metadata records either the actual stop decision or empty candidates.
The statements apply at every work fuel and finite recursive depth.
They do not assert native cache validity, discharge or language semantics.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState InternedConstructorTemplates
open SourceFlatPruningOutputFlow (hookOutputs foldOutputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Core" => EnumerationFlatState.State Symbol Constraint
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}

/-- Classify an output at the cache and metadata recorded when it was emitted. -/
def OutputOrigin (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (output : Output width Typing) : Prop :=
  match output.metadata with
  | some metadata => SourceFlatPruningRestart.decision stop order metadata output.cache = none
  | none => SourceFlatPruningRestart.candidates output.cache = []

private def ParkedSource (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing) :
    SourceFlatPruningSelectedPrefix.Result width Typing → Prop
  | .parked checked candidate raw =>
      raw = candidate.map (fun parked => ExceptT.run
        (SourceFlatPruningRestart.run stop order metadata parked checked)) ∧
      ∀ parked, candidate = some parked → parked.core = checked
  | _ => True

section Prefix
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem parked_source
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (nativeFuel callbackFuel uv : Nat) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    ParkedSource stop order metadata (SourceFlatPruningSelectedPrefix.run holeKey fits admits graph templates
      stop order metadata nativeFuel callbackFuel uv caller before queries) := by
  unfold SourceFlatPruningSelectedPrefix.run
  dsimp only
  split
  · split
    · dsimp only [ParkedSource]
      constructor
      · rfl
      · intro parked completed
        exact SourceFlatPruningIndexAdapters.parked_core _ _ _ _ _ _ _ completed
    · repeat' first | exact True.intro | (dsimp only; split)
    · trivial
  · trivial

/-- A literal parked restart uses the decision at the same framed core passed to recursion. -/
theorem parked_decision
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (nativeFuel callbackFuel uv : Nat) (caller : Caller width)
    (before : Cached) (queries : Queries)
    {checked : Core} {parked : Cached} {updated : Metadata Typing} {next : Option Next} {core : Core}
    (observed : SourceFlatPruningSelectedPrefix.run holeKey fits admits graph templates stop order metadata
      nativeFuel callbackFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    next = SourceFlatPruningRestart.decision stop order updated (EnumerationFlatCached.frame core parked) := by
  have source := parked_source holeKey fits admits graph templates stop order metadata
    nativeFuel callbackFuel uv caller before queries
  rw [observed] at source
  obtain ⟨raw, stored⟩ := source
  simp only [Option.map_some] at raw
  have actual : ExceptT.run (SourceFlatPruningRestart.run stop order metadata parked checked) =
      [.ok ((updated, next), core)] := (Option.some.inj raw).symm
  unfold SourceFlatPruningRestart.run at actual
  split at actual
  · cases actual
  · have item := (List.cons.inj actual).1
    have same := Prod.mk.inj (Except.ok.inj item)
    have metadataSame := (Prod.mk.inj same.1).1
    have nextSame := (Prod.mk.inj same.1).2
    have coreSame : core = parked.core := same.2.symm.trans (stored parked rfl).symm
    have reframed : EnumerationFlatCached.frame core parked = parked := by
      rw [coreSame]
      cases parked
      rfl
    rw [reframed, ← metadataSame]
    exact nextSame.symm

end Prefix
/-- Finishing an actual alternative fold retains every emitted output. -/
theorem finish_outputs (uv : Nat)
    (result : SourceFlatPruningNativeContinuations.Result (Output width Typing) (Failure width Typing) width) :
    hookOutputs (finish uv result) = foldOutputs result := by
  cases result <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem ordinary_finish_outputs
    (property : Output width Typing → Prop)
    (hook : Fragment → Caller width → Queries → Cached →
      SourceFlatPruningNativeContinuations.HookResult (Output width Typing) (Failure width Typing) width)
    (checkEmpty : Bool) (workFuel uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (continued : ∀ fragment reached saved after, ∀ output ∈ hookOutputs (hook fragment reached saved after), property output) :
    ∀ output ∈ hookOutputs (
      let ordinary := SourceFlatPruningNativeOrdinaryContinuations.run hook checkEmpty workFuel workFuel workFuel
        uv edgesOf caller before queries
      match ordinary.2 with
      | none => .stopped [] (.ordinary uv ordinary.1) (some (caller, queries))
      | some folded => finish uv folded), property output := by
  generalize observed : SourceFlatPruningNativeOrdinaryContinuations.run hook checkEmpty workFuel workFuel workFuel
    uv edgesOf caller before queries = ordinary
  obtain ⟨raw, result⟩ := ordinary
  cases result with
  | none =>
      intro output member
      cases member
  | some folded =>
      rw [finish_outputs]
      exact SourceFlatPruningOutputFlow.ordinary_outputs property hook checkEmpty workFuel workFuel workFuel uv
        edgesOf caller before queries continued folded (congrArg Prod.snd observed)

/-- Every emitted resume output belongs to an actual stop or done frontier at its own cache. -/
theorem resume_output_origin
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) (next : Option Next),
      next = SourceFlatPruningRestart.decision stop order metadata before →
      ∀ output ∈ hookOutputs (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel recursiveFuel metadata caller queries before next), OutputOrigin stop order output := by
  induction recursiveFuel with
  | zero =>
      intro metadata caller queries before next selected output member
      cases next with
      | none =>
          simp only [resume, hookOutputs, List.mem_singleton] at member
          subst output
          exact selected.symm
      | some next =>
          cases next with
          | done =>
              simp only [resume, hookOutputs, List.mem_singleton] at member
              subst output
              exact (SourceFlatPruningOutputFrontier.decision_done_iff stop order metadata before).mp selected.symm
          | stuck | expand _ => cases member
  | succ recursiveFuel ih =>
      intro metadata caller queries before next selected
      cases next with
      | none =>
          intro output member
          simp only [resume, hookOutputs, List.mem_singleton] at member
          subst output
          exact selected.symm
      | some next =>
          cases next with
          | done =>
              intro output member
              simp only [resume, hookOutputs, List.mem_singleton] at member
              subst output
              exact (SourceFlatPruningOutputFrontier.decision_done_iff stop order metadata before).mp selected.symm
          | stuck =>
              intro output member
              cases member
          | expand uv =>
              have hookProperty : ∀ (updated : Metadata Typing) (target : Nat) (fragment : Fragment)
                  (reached : Caller width) (saved : Queries) (after : Cached),
                  ∀ (output : Output width Typing), output ∈ hookOutputs (continueWith
                    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
                    graph templates stop order workFuel updated target fragment reached saved after) →
                  OutputOrigin stop order output := by
                intro updated target fragment reached saved after
                unfold continueWith
                apply SourceFlatPruningOutputFlow.continueWith_outputs
                intro current nextCaller nextQueries nextCache
                exact ih current nextCaller nextQueries nextCache _ rfl
              intro output member
              rw [resume] at member
              dsimp only at member
              split at member
              · cases member
              · apply ih _ _ _ _ _ ?_ output member
                apply parked_decision holeKey fits admits graph templates stop order metadata
                  workFuel workFuel uv caller before queries
                assumption
              · cases member
              · cases member
              · exact ordinary_finish_outputs (OutputOrigin stop order) _ checkEmpty workFuel uv edgesOf
                  _ _ _ (hookProperty _ uv) output member
              · cases member
              · cases member

/-- The actual driver discharges the restart-decision condition at every finite bound. -/
theorem run_output_origin
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) :
    ∀ output ∈ hookOutputs (run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before), OutputOrigin stop order output :=
  resume_output_origin holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before _ rfl

end MicroCFTA.SourceFlatPruningRecursive
