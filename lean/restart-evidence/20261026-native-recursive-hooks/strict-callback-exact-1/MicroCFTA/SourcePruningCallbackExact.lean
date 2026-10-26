import MicroCFTA.EnumerationPartialExact
import MicroCFTA.SourcePruningRecordTypes

namespace MicroCFTA.SourcePruningCallbackExact
open Language Fragments EnumerationState EnumerationCorrectness
open SourcePruningPartialMatch SourcePruningTemplates SourcePruningRecordTypes
attribute [local instance] SourcePruningResume.pruningResumeMonadList
attribute [local instance] SourcePruningResume.pruningResumeLawfulMonadList
attribute [local instance] FormulaExecutable.formulaDecidableEq

variable {S G α β : Type}

private theorem pure_exact (value result : α) (before after : State S G)
    (success : Success (pure value) before result after) :
    ExceptT.run ((pure value : EnumerateM S G α) before) = [.ok (result, after)] := by
  obtain ⟨rfl, rfl⟩ := (success_pure value result before after).mp success
  rfl

private theorem mapM_exact (action : α → EnumerateM S G β) (inputs : List α)
    (step : ∀ input before output after, Success (action input) before output after →
      ExceptT.run (action input before) = [.ok (output, after)])
    (before after : State S G) (outputs : List β)
    (success : Success (inputs.mapM action) before outputs after) :
    ExceptT.run ((inputs.mapM action) before) = [.ok (outputs, after)] := by
  induction inputs generalizing before after outputs with
  | nil => exact pure_exact [] outputs before after success
  | cons input rest ih =>
      rw [List.mapM_cons] at success ⊢
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨tail, last, remaining, finished⟩ := (success_bind _ _ _ _ _).mp continued
      rw [bind_single _ _ _ _ _ (step input before output middle first)]
      rw [bind_single _ _ _ _ _ (ih middle last tail remaining)]
      exact pure_exact (output :: tail) outputs last after finished

private theorem part_exact [DecidableEq S] (fuel current : Nat) (term : Term (PartialSymbol S))
    (entry : Template.Pattern S × Nat) (before after : State S G) (result : Option (Pending S))
    (success : Success (representative fuel entry.2 >>= fun root =>
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)]))
      before result after) :
    ExceptT.run ((representative fuel entry.2 >>= fun root =>
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)])) before) =
        [.ok (result, after)] := by
  obtain ⟨root, middle, reading, finished⟩ := (success_bind _ _ _ _ _).mp success
  rw [bind_single _ _ _ _ _
    (EnumerationPartialExact.representative_success_exact fuel entry.2 before middle root reading)]
  exact pure_exact _ result middle after finished

/-- A successful resume reads every pending part and has one exact raw result. -/
theorem resume_exact [DecidableEq S] (fuel current : Nat) (term : Term (PartialSymbol S))
    (pending : Pending S) (before after : State S G) (result : Option (Pending S))
    (success : Success (SourcePruningResume.resume fuel current term pending) before result after) :
    ExceptT.run (SourcePruningResume.resume fuel current term pending before) = [.ok (result, after)] := by
  unfold SourcePruningResume.resume at success ⊢
  obtain ⟨results, middle, traversed, finished⟩ := (success_bind _ _ _ _ _).mp success
  have exactParts := mapM_exact
    (fun entry : Template.Pattern S × Nat => representative fuel entry.2 >>= fun root =>
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)])) pending
    (fun entry previous output next reading => part_exact fuel current term entry previous next output reading)
    before middle results traversed
  rw [bind_single _ _ _ _ _ exactParts]
  exact pure_exact _ result middle after finished

local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Typing : Type}

/-- Every actual successful oracle branch has one exact raw result, including early rejection. -/
theorem oracle_exact (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (pending : List (Pending Symbol)) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (before after : State Symbol Guard) (result : Bool × List (Pending Symbol))
    (success : Success (SourcePruningOracle.oracle graph templates fuel pending uv input) before result after) :
    ExceptT.run (SourcePruningOracle.oracle graph templates fuel pending uv input before) = [.ok (result, after)] := by
  cases input with
  | inr node =>
      rw [SourcePruningOracle.oracle_inr] at success ⊢
      exact pure_exact _ result before after success
  | inl fragment =>
      unfold SourcePruningOracle.oracle at success ⊢
      split at success
      · rename_i early
        rw [ite_eq_left early]
        exact pure_exact _ result before after success
      · rename_i notEarly
        rw [ite_eq_right notEarly]
        split at success
        · rename_i idle
          rw [ite_eq_left idle]
          exact pure_exact _ result before after success
        · rename_i notIdle
          rw [ite_eq_right notIdle]
          change Success (expandPartial graph fuel fragment >>= fun term =>
            pending.mapM (SourcePruningResume.resume fuel uv term) >>= fun resumed =>
              pure (finishChecks resumed (startMatches templates term))) before result after at success
          change ExceptT.run ((expandPartial graph fuel fragment >>= fun term =>
            pending.mapM (SourcePruningResume.resume fuel uv term) >>= fun resumed =>
              pure (finishChecks resumed (startMatches templates term))) before) = [.ok (result, after)]
          obtain ⟨term, middle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨resumed, last, groups, finished⟩ := (success_bind _ _ _ _ _).mp continued
          rw [bind_single _ _ _ _ _
            (EnumerationPartialExact.expandPartial_exact graph fuel fragment before middle term rendered)]
          have exactGroups := mapM_exact (SourcePruningResume.resume fuel uv term) pending
            (fun group previous output next reading => resume_exact fuel uv term group previous next output reading)
            middle last resumed groups
          rw [bind_single _ _ _ _ _ exactGroups]
          exact pure_exact _ result last after finished

/-- An actual successful recording callback has one exact raw metadata and state result. -/
theorem recordTypes_exact (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (before after : State Symbol Guard) (result : Bool × Metadata Typing)
    (success : Success (recordTypes graph templates fuel metadata uv input) before result after) :
    ExceptT.run (recordTypes graph templates fuel metadata uv input before) = [.ok (result, after)] := by
  cases templates with
  | nil =>
      rw [recordTypes_empty] at success ⊢
      exact pure_exact _ result before after success
  | cons first rest =>
      change Success (SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv input >>= fun observed =>
        pure (observed.1, {metadata with pending := observed.2, types := updatedTypes metadata uv input}))
        before result after at success
      change ExceptT.run ((SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv input >>= fun observed =>
        pure (observed.1, {metadata with pending := observed.2, types := updatedTypes metadata uv input})) before) =
          [.ok (result, after)]
      obtain ⟨observed, middle, reading, finished⟩ := (success_bind _ _ _ _ _).mp success
      rw [bind_single _ _ _ _ _ (oracle_exact graph (first :: rest) fuel metadata.pending uv input
        before middle observed reading)]
      exact pure_exact _ result middle after finished

end MicroCFTA.SourcePruningCallbackExact
