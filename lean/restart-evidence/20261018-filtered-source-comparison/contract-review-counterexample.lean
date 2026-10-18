import MicroCFTA.SourceCurrentNativeBinderProfile
import MicroCFTA.SourceCurrentScopedProfileInputs
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.FilteredProfileContractBoundary
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile profile Equivalent)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (shadow Correct)

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

end MicroCFTA.FilteredProfileContractBoundary
