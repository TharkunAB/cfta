import MicroCFTA.SourcePhysicalSharedRowsTraversal
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedStoredSubstitutionScope

/-!
# Actual exposure of a productive single recursive knot

The fragment is mu x. (base | step x). Its body contains one nullary edge
and one unary edge to its own stored reference. The proof executes current
stored substitution and actual edge and node interning. Nested Mu and union
closure are outside this fragment.
-/
namespace MicroCFTA.SourcePhysicalRecursiveRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome work)

/-- The original stored body keeps its exact edge entries and recursive reference. -/
def body (identity : Nat) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) : Value Symbol Unit :=
  .node entry [.mk base [], .mk step [.reference (.interned identity)]] 0 [.interned identity]

/-- The complete source knot includes its actual cached probe records. -/
def knot (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary : Value Symbol Unit) : Value Symbol Unit :=
  .mu entry (body entry.identity bodyEntry base step) depth ordinary

/-- This stored knot is closed by its actual cached free metadata. -/
theorem knot_closed (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary : Value Symbol Unit) :
    (knot entry bodyEntry base step depth ordinary).free = [] := by
  simp [knot, body, Value.free]

/-- Source unfolding rebuilds the two concrete edge requests before normalizing their node. -/
def rebuild (root : Value Symbol Unit) (base step : Symbol) : Work Symbol Unit (Value Symbol Unit) :=
  (makeEdge base () []).bind fun first =>
    (makeEdge step () [root]).bind fun second => makeNode [first, second]

/-- The body prepares no dynamic nested binder request. -/
theorem body_prepared (identity : Nat) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) :
    InternedStoredClosedMuCompletion.PreparedWithoutMu (body identity entry base step) := by
  apply InternedStoredClosedMuCompletion.PreparedWithoutMu.node
  intro child member
  have same : child = .reference (.interned identity) := by simpa [EdgeValue.children] using member
  rw [same]
  exact .reference _

/-- The old stored executor performs exactly the two physical edge effects and node readback. -/
theorem unfold_work [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary : Value Symbol Unit) (state : State Symbol Unit) :
    InternedStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) state =
      work (rebuild (knot entry bodyEntry base step depth ordinary) base.key.symbol step.key.symbol) state := by
  have baseConstraint : base.key.constraint = () := Subsingleton.elim _ _
  have stepConstraint : step.key.constraint = () := Subsingleton.elim _ _
  simp [InternedStoredSubstitution.unfold, knot, InternedStoredSubstitution.execute, body,
    InternedStoredSubstitution.leaves, InternedStoredSubstitution.edgeLeaves, InternedStoredSubstitution.manyLeaves,
    InternedStoredSubstitution.encode, InternedStoredSubstitution.encodeEdges, InternedStoredSubstitution.encodeMany,
    InternedStoredSubstitution.slot, InternedStoredSubstitution.input, Value.free,
    InternedNestedConstruction.build, InternedNestedConstruction.buildEdges, InternedNestedConstruction.buildMany,
    Outcome.bind, work, rebuild, run_bind, List.findIdx, List.findIdx.go, Value.referenceOf, baseConstraint, stepConstraint]

/-- Current repaired unfolding has the identical returned record and final cache. -/
theorem current_unfold_work [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary : Value Symbol Unit) (state : State Symbol Unit) :
    InternedFreshOrdinaryStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) state =
      work (rebuild (knot entry bodyEntry base step depth ordinary) base.key.symbol step.key.symbol) state := by
  exact (InternedFreshOrdinaryStoredSubstitution.unfold_mu_eq entry _ depth ordinary state
    (body_prepared entry.identity bodyEntry base step)).trans (unfold_work entry bodyEntry base step depth ordinary state)

end MicroCFTA.SourcePhysicalRecursiveRows
