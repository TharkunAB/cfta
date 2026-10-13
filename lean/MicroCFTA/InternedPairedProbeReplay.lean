import MicroCFTA.InternedFreeAbsenceReplay

/-!
# Exact replay of both normalized source probes

Change one interned captured literal to another reference.
Absence from both completed probes gives equality of the complete probe pair.
The Depth equality also identifies the actual ordinary callback arguments.
-/
namespace MicroCFTA.InternedPairedProbeReplay
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback
open InternedFreeAbsenceContext InternedFreeAbsenceReplay InternedRequestAgreement
open InternedBinderProtocol (Reference)

/-- Both actual normalized probes replay across one captured interned-name replacement. -/
theorem pair_equal [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (identity : Nat) (replacement : Reference) (names : List Reference)
    (left right common afterLeftDepth afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left names) (rc : Context right (names.map (change identity replacement)))
    (coherent : Coherent common) (leftDepth leftOrdinary rightDepth rightOrdinary : Value Symbol Guard)
    (leftDepthDone : callback body (names.map Value.reference) .depth left = .done leftDepth afterLeftDepth)
    (leftOrdinaryDone : callback body (names.map Value.reference) (.uninterned leftDepth.depth) afterLeftDepth = .done leftOrdinary afterLeft)
    (rightDepthDone : callback body ((names.map (change identity replacement)).map Value.reference) .depth right = .done rightDepth afterRightDepth)
    (rightOrdinaryDone : callback body ((names.map (change identity replacement)).map Value.reference) (.uninterned rightDepth.depth) afterRightDepth = .done rightOrdinary afterRight)
    (leftGrowth : Grows afterLeft common) (rightGrowth : Grows afterRight common)
    (depthAbsent : .interned identity ∉ leftDepth.free) (ordinaryAbsent : .interned identity ∉ leftOrdinary.free) :
    leftDepth = rightDepth ∧ leftOrdinary = rightOrdinary := by
  have leftDepthContext : Context afterLeftDepth names := by
    simpa only [leftDepthDone, Outcome.state] using lc.callback body .depth (depth_available left)
  have rightDepthContext : Context afterRightDepth (names.map (change identity replacement)) := by
    simpa only [rightDepthDone, Outcome.state] using rc.callback body .depth (depth_available right)
  have leftOrdinaryGrowth : Grows afterLeftDepth afterLeft := by
    simpa only [leftOrdinaryDone, Outcome.state] using
      (callback_growing body (names.map Value.reference) (.uninterned leftDepth.depth)
        afterLeftDepth leftDepthContext.normal.facts.coherent.valid).2
  have rightOrdinaryGrowth : Grows afterRightDepth afterRight := by
    simpa only [rightOrdinaryDone, Outcome.state] using
      (callback_growing body ((names.map (change identity replacement)).map Value.reference) (.uninterned rightDepth.depth)
        afterRightDepth rightDepthContext.normal.facts.coherent.valid).2
  have depthSame := callback_equal body identity replacement (build_related body identity replacement) names .depth
    (by intro impossible; cases impossible) left right common afterLeftDepth afterRightDepth lc rc coherent
    (depth_available left) (depth_available right) leftDepth rightDepth leftDepthDone rightDepthDone
    (grows_trans leftOrdinaryGrowth leftGrowth) (grows_trans rightOrdinaryGrowth rightGrowth) depthAbsent
  subst rightDepth
  exact ⟨rfl, callback_equal body identity replacement (build_related body identity replacement) names
    (.uninterned leftDepth.depth) (by intro impossible; cases impossible)
    afterLeftDepth afterRightDepth common afterLeft afterRight leftDepthContext rightDepthContext coherent
    (ordinary_available afterLeftDepth leftDepth.depth) (ordinary_available afterRightDepth leftDepth.depth)
    leftOrdinary rightOrdinary leftOrdinaryDone rightOrdinaryDone leftGrowth rightGrowth ordinaryAbsent⟩

end MicroCFTA.InternedPairedProbeReplay
