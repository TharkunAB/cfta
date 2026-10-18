import MicroCFTA.SourceCurrentCausalSourceNodeComparison
import MicroCFTA.SourceCurrentCausalSourceUnionComparison
import MicroCFTA.SourceCurrentCausalSourceBinderComparison
import MicroCFTA.SourceCurrentCausalPublicationProfile

/-!
# Complete causal root comparison and actual payload initialization

Syntax induction proves comparison for every source form. The law keeps
its actual calls, live input agreements and common causal reader explicit.
Chronological publication induction then derives the payload contract
from empty tables. It does not assume that contract for new candidates.
This result concerns root profiles. It does not prove general completion
or agreement of all deeper guarded language observations.
-/
namespace MicroCFTA.SourceCurrentCausalSourceComparison
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceCurrentCausalSourceRootLaw (Law)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentPublicationHeapInduction (Heap)
open SourceCurrentStoredMuProfileContract (Correct)

/-- All source forms preserve assigned profiles after aligned original root deletion. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) : Law expression := by
  generalize measure : sizeOf expression = bound
  induction bound using Nat.strongRecOn generalizing expression with
  | ind bound ih =>
      cases expression with
      | empty => exact SourceCurrentCausalSourceRootLaw.empty
      | var index => exact SourceCurrentCausalSourceRootLaw.var index
      | union expressions =>
          apply SourceCurrentCausalSourceUnionComparison.union expressions
          intro child member
          have smaller : sizeOf child < bound := by
            have inside := List.sizeOf_lt_of_mem member
            simp only [Syntax.union.sizeOf_spec] at measure
            omega
          exact @ih (sizeOf child) smaller child rfl
      | node rows =>
          apply SourceCurrentCausalSourceNodeComparison.node rows
          intro symbol guard children member child included
          have smaller : sizeOf child < bound := by
            have outer := List.sizeOf_lt_of_mem member
            have inner := List.sizeOf_lt_of_mem included
            simp only [Syntax.node.sizeOf_spec] at measure
            simp only [EdgeSyntax.mk.sizeOf_spec] at outer
            omega
          exact @ih (sizeOf child) smaller child rfl
      | binder smart body =>
          apply SourceCurrentCausalSourceBinderComparison.binder smart body
          have smaller : sizeOf body < bound := by
            simp only [Syntax.binder.sizeOf_spec] at measure
            omega
          exact @ih (sizeOf body) smaller body rfl

/-- Earlier causal payload facts prove each actual candidate before its publication. -/
theorem publication [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (earlier : Heap Correct event.afterBody) (history : History empty event.afterBody) :
    Correct event.entry event.body event.depth event.ordinary :=
  SourceCurrentCausalPublicationProfile.publication event (source event.expression) earlier history

/-- Actual source execution preserves its payload heap through every complete or pending prefix. -/
theorem build_heap [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (history : History empty state) (initial : Heap Correct state) :
    Heap Correct (InternedFreshOrdinaryConstruction.build expression environment state).state :=
  SourceCurrentCausalPublicationProfile.build source expression environment state context history initial

/-- Closed source construction derives its entire payload heap from empty tables. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap Correct (InternedFreshOrdinaryConstruction.build expression [] empty).state :=
  SourceCurrentCausalPublicationProfile.closed source expression

/-- Every actual completed closed construction has the derived payload contract for all stored records. -/
theorem constructed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build expression [] empty = .done value after) :
    Heap Correct after := by
  simpa only [actual,Outcome.state] using closed_heap expression

end MicroCFTA.SourceCurrentCausalSourceComparison
