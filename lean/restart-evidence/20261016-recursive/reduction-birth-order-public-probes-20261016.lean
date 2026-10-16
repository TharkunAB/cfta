import MicroCFTA.SourceCurrentReductionBirthOrder
open MicroCFTA SourceCurrentReductionBirthOrder
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.recordRound_lookup
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.birthsFrom_lookup
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.births_lookup
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.occurs_lower
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.locateRound_origin
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.locateRound_le
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.locateRound_none
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.births_exact
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.births_bound
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.merge_exact
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.fromMinEntries_none
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.fromMinEntries_origin
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.fromMinEntries_le
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.fromMinEntries_exact
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.merge_none
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.merge_assoc
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.foldMin_lookup
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.transportEntries_mem
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.rounds_fold
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.rounds_exact
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.locateRound_rename
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.births_rename
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.fromMinEntries_rename
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.transportEntries_rename
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.rounds_rename
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.history_rounds_rename
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.rounds_bound
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.index_unknown
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.known_before_fallback
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.known_before_unknown
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.reductions_length
#print axioms MicroCFTA.SourceCurrentReductionBirthOrder.source_history_bound
#check @MicroCFTA.SourceCurrentReductionBirthOrder.birthsFrom_lookup
#check @MicroCFTA.SourceCurrentReductionBirthOrder.births_exact
#check @MicroCFTA.SourceCurrentReductionBirthOrder.fromMinEntries_exact
#check @MicroCFTA.SourceCurrentReductionBirthOrder.foldMin_lookup
#check @MicroCFTA.SourceCurrentReductionBirthOrder.transportEntries_mem
#check @MicroCFTA.SourceCurrentReductionBirthOrder.rounds_exact
#check @MicroCFTA.SourceCurrentReductionBirthOrder.rounds_rename
#check @MicroCFTA.SourceCurrentReductionBirthOrder.history_rounds_rename
#check @MicroCFTA.SourceCurrentReductionBirthOrder.known_before_unknown
#check @MicroCFTA.SourceCurrentReductionBirthOrder.source_history_bound

namespace BirthOrderKernels
-- 1. Source birth indices count rounds, not edges within a round.
example : births ([[1, 2, 1], [2, 3]] : List (List Int)) 2 = some 0 := by decide
-- 2. Later rounds preserve the first birth of an existing edge.
example : births ([[1], [2], [1]] : List (List Int)) 1 = some 0 := by decide
-- 3. Signed keys remain literal table keys.
example : births ([[-7], [2, -7]] : List (List Int)) (-7) = some 0 := by decide
-- 4. Refold collisions retain the earliest preimage, independent of observation order.
example : rounds (births ([[1], [2], [3]] : List (List Int))) [(3, 9), (1, 9)] 9 = some 0 := by decide
-- 5. An earlier original birth survives a later mapped birth.
example : rounds (births ([[9], [1]] : List (List Int))) [(1, 9)] 9 = some 0 := by decide
-- 6. An earlier mapped birth replaces a later original birth. The union is minimum, not left biased.
example : rounds (births ([[1], [9]] : List (List Int))) [(1, 9)] 9 = some 0 := by decide
-- 7. A refold preimage absent from the original birth table supplies no entry.
example : rounds (births ([[1]] : List (List Int))) [(404, 9)] 9 = none := by decide
-- 8. The literal minimum insertion fold computes the same colliding value.
example : foldMin ([(9, 2), (9, 0), (9, 1)] : List (Int × Nat)) (fun _ => none) 9 = some 0 := by decide
-- 9. Unknown edges use the full history length, after every known edge.
example : index 3 (rounds (births ([[1], [2], [3]] : List (List Int))) [(1, 9)]) 999 = 3 ∧
    index 3 (rounds (births ([[1], [2], [3]] : List (List Int))) [(1, 9)]) 9 < 3 := by decide
-- 10. A key renaming can reverse signed key order and preserve the proved lookup.
example (history : List (List Int)) (edges : List (Int × Int)) (key : Int) :
    rounds (births (history.map (List.map (fun value => -value))))
      (edges.map (fun edge => (-edge.1, -edge.2))) (-key) = rounds (births history) edges key := by
  apply history_rounds_rename (fun value : Int => -value)
  intro first second same
  exact Int.neg_inj.mp same
-- 11. A noninjective rename can change the first birth. Injectivity is necessary.
example : births (([[1], [2]] : List (List Int)).map (List.map (fun _ => (0 : Int)))) 0 ≠
    births ([[1], [2]] : List (List Int)) 2 := by decide
-- 12. A stable reduction returns its single input space.
example : reductions (fun value : Nat => value) 30 7 = [7] := by decide
-- 13. An always-changing reduction still has exactly the fixed maximum of 31 spaces.
example : (reductions (fun value : Nat => value + 1) 30 0).length = 31 := by decide
-- 14. Arbitrary public histories are not constrained to the fixed reduction bound.
example : (List.replicate 40 ([] : List Int)).length > 31 := by decide
end BirthOrderKernels
