import MicroCFTA.SourceCurrentStoredRootDeletionFilter
import MicroCFTA.SourceCurrentNativeBinderProfile
import MicroCFTA.SourceCurrentScopedProfileInputs
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RootDeletionFilterIntegration
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile profile Equivalent)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (shadow Correct)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentStoredFilteredProfile (filtered)
open SourceEqualityRequiredCache (Ready Keeps)

private def result (call : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match call with | .done value _ => value | .pending .. => .empty
private def x : Reference := .uninterned 10
private def z : Reference := .uninterned 11
private def inputs : List (Value Nat Bool) := [.reference x,.reference z]
private def aSyntax : Syntax Nat Bool :=
  .union [.var 0,.node [.mk 7 false [.var 0,.var 1]],.binder false (.var 2)]
private def bSyntax : Syntax Nat Bool :=
  .binder false (.union [.var 1,.var 2,.node [.mk 7 false [.var 1,.var 2]]])
private def aCall := build aSyntax inputs empty
private def a := result aCall
private def aHeap := aCall.state
private def bCall := build bSyntax inputs aHeap
private def b := result bCall
private def reader := bCall.state
private def filteredA := (run (withoutSelfReference x a) reader).1
private def filteredB := (run (withoutSelfReference x b) reader).1
private def assignment (name : Reference) : Profile :=
  if name = x then some [.uninterned 30] else some []

private theorem a_done : build aSyntax inputs empty = .done a aHeap := by cbv
private theorem b_done : build bSyntax inputs aHeap = .done b reader := by cbv

private theorem same (rho : Reference → Profile) : Equivalent (denote a rho) (denote b rho) := by
  cases hx : rho (.uninterned 10) with
  | none =>
      cases hz : rho (.uninterned 11) with
      | none => cbv; simp [hx,hz]
      | some zs => cases zs <;> cbv <;> simp [hx,hz]
  | some xs =>
      cases xs with
      | nil =>
          cases hz : rho (.uninterned 11) with
          | none => cbv; simp [hx,hz]
          | some zs => cases zs <;> cbv <;> simp [hx,hz]
      | cons first rest =>
          cases hz : rho (.uninterned 11) with
          | none => cbv; simp [hx,hz]
          | some zs => cases zs <;> cbv <;> simp [hx,hz]

private theorem different : ¬ Equivalent (denote filteredA assignment) (denote filteredB assignment) := by
  cbv
  simp


private theorem source_keeps (expression : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before : State Nat Bool) (initial : Ready before) (available : InternedNestedProvenance.Values before inputs)
    (result : Value Nat Bool) (after : State Nat Bool) (actual : build expression inputs before = .done result after) : Keeps before after := by
  have checked := InternedFreshOrdinaryFacts.build_verified expression inputs before initial.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before initial.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before initial.semantic.1.normal.facts.coherent.valid initial.covered result after actual
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth expression inputs before
      (SourceRecursiveIntersectionSemanticHeap.context before initial.semantic inputs available) initial.semantic.2 initial.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history

private theorem captures_available (state : State Nat Bool) : InternedNestedProvenance.Values state inputs := by
  intro value member
  have choices : value = .reference x ∨ value = .reference z := by
    simpa only [inputs,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl <;> exact InternedNestedProvenance.ordinary_available state _
private theorem initial_ready : Ready (empty : State Nat Bool) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty (by rw [build])
private theorem first_keeps : Keeps empty aHeap :=
  source_keeps aSyntax inputs empty initial_ready (captures_available empty) a aHeap a_done
private theorem second_keeps : Keeps aHeap reader :=
  source_keeps bSyntax inputs aHeap first_keeps.ready (captures_available aHeap) b reader b_done
private theorem a_available : Available reader a :=
  second_keeps.available a ((InternedFreshOrdinaryFacts.build_verified aSyntax inputs empty
    initial_ready.semantic.1.normal.facts (captures_available empty)).result a aHeap a_done)
private theorem b_available : Available reader b :=
  (InternedFreshOrdinaryFacts.build_verified bSyntax inputs aHeap first_keeps.ready.semantic.1.normal.facts
    (captures_available aHeap)).result b reader b_done
private theorem a_not_bare : (a.referenceOf == .ref x) = false := by cbv
private theorem b_not_bare : (b.referenceOf == .ref x) = false := by cbv
private theorem a_deleted : filtered x a assignment = deleted (fun name => name == x) a assignment := by
  simpa only [a_not_bare,Bool.false_eq_true,ite_false] using
    SourceCurrentStoredRootDeletionFilter.singleton x a assignment reader second_keeps.ready.semantic.1.normal a_available
private theorem b_deleted : filtered x b assignment = deleted (fun name => name == x) b assignment := by
  simpa only [b_not_bare,Bool.false_eq_true,ite_false] using
    SourceCurrentStoredRootDeletionFilter.singleton x b assignment reader second_keeps.ready.semantic.1.normal b_available
private theorem deleted_different : ¬ Equivalent (deleted (fun name => name == x) a assignment)
    (deleted (fun name => name == x) b assignment) := by
  cbv
  simp
private theorem a_filter : Equivalent (denote filteredA assignment) (deleted (fun name => name == x) a assignment) := by
  simpa only [filteredA,a_not_bare,Bool.false_eq_true,ite_false] using
    SourceCurrentStoredRootDeletionFilter.filter_profile x a assignment reader second_keeps.ready a_available
private theorem b_filter : Equivalent (denote filteredB assignment) (deleted (fun name => name == x) b assignment) := by
  simpa only [filteredB,b_not_bare,Bool.false_eq_true,ite_false] using
    SourceCurrentStoredRootDeletionFilter.filter_profile x b assignment reader second_keeps.ready b_available

private theorem checked :
    ∃ (first second : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (left right : Value Nat Bool) (middle final : State Nat Bool)
      (name : Reference) (rho : Reference → Profile),
      build first captures empty = .done left middle ∧
      build second captures middle = .done right final ∧
      Ready final ∧ Available final left ∧ Available final right ∧
      (∀ assignment, Equivalent (denote left assignment) (denote right assignment)) ∧
      ¬ Equivalent (deleted (fun n => n == name) left rho) (deleted (fun n => n == name) right rho) ∧
      filtered name left rho = deleted (fun n => n == name) left rho ∧
      filtered name right rho = deleted (fun n => n == name) right rho ∧
      Equivalent (denote (run (withoutSelfReference name left) final).1 rho)
        (deleted (fun n => n == name) left rho) ∧
      Equivalent (denote (run (withoutSelfReference name right) final).1 rho)
        (deleted (fun n => n == name) right rho) ∧
      deleted (fun n => n == name) (.reference name : Value Nat Bool) rho = some [] ∧
      denote (run (withoutSelfReference name (.reference name : Value Nat Bool)) final).1 rho = some [.uninterned 30] := by
  exact ⟨aSyntax,bSyntax,inputs,a,b,aHeap,reader,x,assignment,a_done,b_done,
    second_keeps.ready,a_available,b_available,same,deleted_different,a_deleted,b_deleted,a_filter,b_filter,
    (by cbv),(by cbv)⟩

/-- Root deletion distinguishes the actual source boundary and keeps the bare-self exception explicit. -/
theorem actual_boundary :
    ∃ (first second : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (left right : Value Nat Bool) (middle final : State Nat Bool)
      (name : Reference) (rho : Reference → Profile),
      build first captures empty = .done left middle ∧
      build second captures middle = .done right final ∧
      Ready final ∧ Available final left ∧ Available final right ∧
      (∀ assignment, Equivalent (denote left assignment) (denote right assignment)) ∧
      ¬ Equivalent (deleted (fun n => n == name) left rho) (deleted (fun n => n == name) right rho) ∧
      filtered name left rho = deleted (fun n => n == name) left rho ∧
      filtered name right rho = deleted (fun n => n == name) right rho ∧
      Equivalent (denote (run (withoutSelfReference name left) final).1 rho)
        (deleted (fun n => n == name) left rho) ∧
      Equivalent (denote (run (withoutSelfReference name right) final).1 rho)
        (deleted (fun n => n == name) right rho) ∧
      deleted (fun n => n == name) (.reference name : Value Nat Bool) rho = some [] ∧
      denote (run (withoutSelfReference name (.reference name : Value Nat Bool)) final).1 rho = some [.uninterned 30] := checked

end MicroCFTA.RootDeletionFilterIntegration
