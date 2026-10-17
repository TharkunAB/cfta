import MicroCFTA.SourceCurrentPrimaryReplay
import MicroCFTA.SourceCurrentRequiredExposureSafe
import MicroCFTA.SourceCurrentRequiredSupport

/-!
# Primary certificates for structural Required inputs

False primary certificates retain their recursive acceptance facts.
Each original path replays at the completed heap. The secondary gate
does not supply this stronger certificate for a closed constrained Mu.
-/
namespace MicroCFTA.SourceCurrentRequiredPrimaryExposure
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (ExposureSafe)
open SourceCurrentRequiredSupport (Tip)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
noncomputable local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.decEq _

/-- Every row in a false primary scan retains its child certificate at later heaps. -/
theorem false_edges_members
    (index : Nat) (path : EqualityNormalize.Path) (edges : List (EdgeValue Symbol Guard))
    (before after : Heap) (trace : EdgesTrace source reaches index path edges before false after)
    (semantic : SemanticReady before) (available : Values before (edges.flatMap EdgeValue.children))
    (target : Heap) (retained : Grows after target) :
    ∀ edge ∈ edges, ChildTrace source reaches edge.children index path target false target := by
  induction edges generalizing before with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      cases trace with
      | next head tail =>
          have firstEffects := SourceCurrentPrimaryReplay.child_replay source reaches _ _ _ _ _ _ head semantic
            (fun value member => available value (by simp [member]))
          have tailAvailable : Values _ (rest.flatMap EdgeValue.children) :=
            fun value member => firstEffects.2.1.available value (available value (by simp [member]))
          have tailEffects := SourceCurrentPrimaryReplay.edges_replay source reaches _ _ _ _ _ _ tail firstEffects.1 tailAvailable
          intro edge member
          rcases List.mem_cons.mp member with rfl | member
          · exact firstEffects.2.2 target (grows_trans tailEffects.2.1.growth retained)
          · exact ih _ tail firstEffects.1 tailAvailable edge member

/-- An existing selected slot retains the exact primary node certificate. -/
theorem false_selected
    {values : List (Value Symbol Guard)} {index : Nat} {path : EqualityNormalize.Path}
    {value : Value Symbol Guard} {before after : Heap}
    (trace : ChildTrace source reaches values index path before false after)
    (found : values[index]? = some value) : NodeTrace source reaches path value before false after := by
  cases trace with
  | missing absent => rw [absent] at found; cases found
  | present selected node =>
      have same := Option.some.inj (selected.symm.trans found)
      cases same
      exact node

/-- Every original path in a false class retains its primary certificate at later heaps. -/
theorem false_class_paths
    (values : List (Value Symbol Guard)) (paths : Class) (before after : Heap)
    (trace : ClassTrace source reaches values paths before false after)
    (semantic : SemanticReady before) (available : Values before values)
    (target : Heap) (retained : Grows after target) :
    ∀ path ∈ paths, PathTrace source reaches values path target false target := by
  induction paths generalizing before with
  | nil => intro path member; cases member
  | cons first rest ih =>
      cases trace with
      | next head tail =>
          have firstEffects := SourceCurrentPrimaryReplay.path_replay source reaches _ _ _ _ _ head semantic available
          have tailAvailable := fun value member => firstEffects.2.1.available value (available value member)
          have tailEffects := SourceCurrentPrimaryReplay.class_replay source reaches _ _ _ _ _ tail firstEffects.1 tailAvailable
          intro path member
          rcases List.mem_cons.mp member with rfl | member
          · exact firstEffects.2.2 target (grows_trans tailEffects.2.1.growth retained)
          · exact ih _ tail firstEffects.1 tailAvailable path member

end MicroCFTA.SourceCurrentRequiredPrimaryExposure
