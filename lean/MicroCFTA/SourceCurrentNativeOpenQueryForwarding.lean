import MicroCFTA.SourceCurrentNativeQueryRowOrigins

/-!
# Actual native forwarding for open operands

Codec witnesses replace closedness in swap and reset normalization.
The existing Route retains exact captured calls and the final reader.
The terminal request retains both codecs and its protected earlier writer.
-/
namespace MicroCFTA.SourceCurrentNativeOpenQueryForwarding
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeQueryRowOrigins (Route)
open SourceRecursiveIntersectionControl (decision reset greater)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

private theorem payload_not_forward (left right : Value Symbol Guard) :
    SourceRecursiveIntersectionControl.payload left right ≠ .swap ∧
    SourceRecursiveIntersectionControl.payload left right ≠ .reset := by
  cases left <;> cases right <;> simp [SourceRecursiveIntersectionControl.payload]

private theorem swap_tests (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .swap) :
    reset request.domain.key request.left request.right = false ∧ greater request.left request.right = true := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · rename_i restart
      split at selected
      · cases selected
      · split at selected
        · exact ⟨Bool.eq_false_iff.mpr restart,by assumption⟩
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact False.elim ((payload_not_forward request.left request.right).1 selected)

private theorem reset_test (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .reset) :
    reset request.domain.key request.left request.right = true := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · assumption
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact False.elim ((payload_not_forward request.left request.right).2 selected)

private def measure (request : NodeRequest Symbol Guard) : Nat :=
  if reset request.domain.key request.left request.right then 2 else if greater request.left request.right then 1 else 0

private theorem swap_decreases (request : NodeRequest Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (selected : decision request.domain.key request.left request.right = .swap) :
    measure ⟨request.domain,request.right,request.left⟩ < measure request := by
  obtain ⟨restart,ordered⟩ := swap_tests request selected
  obtain ⟨first,firstInput⟩ := left
  obtain ⟨second,secondInput⟩ := right
  have reversed := SourceRecursiveIntersectionSchedule.swap_once request.left request.right first second firstInput secondInput ordered
  have same : reset request.domain.key request.right request.left = false := by
    simpa only [reset,Bool.and_assoc,Bool.and_left_comm] using restart
  simp only [measure,restart,ordered,same,reversed,Bool.false_eq_true,ite_false,ite_true]
  decide

private theorem reset_decreases (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .reset) :
    measure ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ < measure request := by
  have restart := reset_test request selected
  simp only [measure,restart,ite_true]
  simp only [reset,IntersectionEmptyDomain.emptyDomain,IntersectionEmptyDomain.emptyKey,
    List.isEmpty_nil,Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false]
  split <;> decide

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem forwarded_returned {before after reader : Checked width}
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (forwarded : SourceCurrentNativeForwardLineage.Forwarded reader request before after result) :
    ∃ handle, reader.native.nodes.cells handle = some ⟨request,.returned result⟩ := by
  rcases forwarded.2 with ⟨unresolved,_⟩ | ⟨handle,present,_⟩
  · obtain ⟨first,firstInput⟩ := left
    obtain ⟨second,secondInput⟩ := right
    have key := IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ first second firstInput secondInput
    change IntersectionFlatMemoKeyDomain.sourceKey width request.domain request.left.referenceOf request.right.referenceOf = none at unresolved
    rw [key] at unresolved
    cases unresolved
  · exact ⟨handle,present⟩

/-- Actual swap and reset writers reach a terminal writer while retaining both operand codecs. -/
theorem normalize {reader : Checked width} (history : History reader)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (left : ∃ first, IntersectionFlatMemoKey.input request.left.referenceOf = some first)
    (right : ∃ second, IntersectionFlatMemoKey.input request.right.referenceOf = some second)
    (returned : ∃ handle,reader.native.nodes.cells handle = some ⟨request,.returned result⟩) :
    ∃ terminal handle, Route reader result request terminal ∧
      reader.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle terminal result reader.native ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
      decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
      (∃ first, IntersectionFlatMemoKey.input terminal.left.referenceOf = some first) ∧
      (∃ second, IntersectionFlatMemoKey.input terminal.right.referenceOf = some second) := by
  generalize boundEq : measure request = bound
  induction bound using Nat.strongRecOn generalizing request with
  | ind bound ih =>
    obtain ⟨handle,present⟩ := returned
    have writer := SourceCurrentNativeWriterReadyRetention.writers history handle request result present
    by_cases swap : decision request.domain.key request.left request.right = .swap
    · obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,retained⟩ := writer
      have forwarded := SourceCurrentNativeForwardLineage.swap history request fuel result good actual retained swap
      obtain ⟨next,stored⟩ := forwarded_returned _ result right left forwarded
      obtain ⟨terminal,final,route,cell,written,notSwap,notReset,firstCodec,secondCodec⟩ := ih _
        (by rw [← boundEq]; exact swap_decreases request left right swap)
        ⟨request.domain,request.right,request.left⟩ right left ⟨next,stored⟩ rfl
      exact ⟨terminal,final,.step ⟨before,after,fuel,good,actual,retained,.inl ⟨swap,rfl⟩,forwarded⟩ route,
        cell,written,notSwap,notReset,firstCodec,secondCodec⟩
    · by_cases restart : decision request.domain.key request.left request.right = .reset
      · obtain ⟨before,after,fuel,good,_,_,actual,_,_,_,_,retained⟩ := writer
        have forwarded := SourceCurrentNativeForwardLineage.reset history request fuel result good actual retained restart
        obtain ⟨next,stored⟩ := forwarded_returned
          ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ result left right forwarded
        obtain ⟨terminal,final,route,cell,written,notSwap,notReset,firstCodec,secondCodec⟩ := ih _
          (by rw [← boundEq]; exact reset_decreases request restart)
          ⟨IntersectionEmptyDomain.emptyDomain,request.left,request.right⟩ left right ⟨next,stored⟩ rfl
        exact ⟨terminal,final,.step ⟨before,after,fuel,good,actual,retained,.inr ⟨restart,rfl⟩,forwarded⟩ route,
          cell,written,notSwap,notReset,firstCodec,secondCodec⟩
      · exact ⟨request,handle,.refl request,present,writer,swap,restart,left,right⟩

end MicroCFTA.SourceCurrentNativeOpenQueryForwarding
