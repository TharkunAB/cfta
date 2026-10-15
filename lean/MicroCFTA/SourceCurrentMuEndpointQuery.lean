import MicroCFTA.SourceCurrentMuEndpointMemos
import MicroCFTA.SourceRefusedClassQuery
import MicroCFTA.SourceCurrentEmptinessDecision

/-!
# Sound queries for classes that end at closed records

The new secondary rule admits a closed constrained Mu endpoint. Original
siblings outside the selected class can remain open. The selected endpoint
records derive the existing projection domain. Actual seeded native steps
and a completed guarded emptiness body then refute a satisfied active class.
This is a source-policy subclass. It is not a general lift of every new
false secondary trace. Global emptiness memo lookup, GHC demand, and native
containers remain separate source boundaries.
-/
namespace MicroCFTA.SourceCurrentMuEndpointQuery
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityProjectionGraph (select)
open SourceEqualityProjectionPathDomain (NodeClosed ForestClosed)
open SourceCurrentMuEndpoint
open SourceEqualityNativeScoped SourceEmptinessClassFold
open InternedGuardedLanguage (meaning)

/-- Actual selected closed endpoints derive the path-local signed projection domain. -/
theorem endpoints_domain (values : List (Value Symbol Guard)) (paths : Class)
    (endpoints : ClosedEndpoints values paths) :
    ∀ path ∈ paths, ForestClosed (path.map Int.ofNat) values := by
  intro path member
  obtain ⟨index, value, rfl, selected, endpoint⟩ := endpoints path member
  simp only [List.map_cons, List.map_nil, ForestClosed]
  intro child found
  have selectedChild : values[index]? = some child := by simpa [select] using found
  have same := Option.some.inj (selectedChild.symm.trans selected)
  subst child
  simpa only [NodeClosed] using endpoint.closed

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- The new secondary policy and an actual true seeded-query decision refute such an original class. -/
theorem refutes_decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (paths : Class) (active : Nontrivial paths) (values : List (Value Symbol Guard))
    (endpoints : ClosedEndpoints values paths)
    {query : Value Symbol Guard} {before middle after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (seeded : Seeded top conjoin values (paths.map (List.map Int.ofNat)) before query middle)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (decision : SourceCurrentEmptinessDecision.Decision query middle true after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    classMeets false source reaches (fuel + 1) values paths before.machine.heap = .done (some false) before.machine.heap ∧
    ¬ClassSat (.node symbol terms) paths := by
  constructor
  · exact closed_endpoints_class source reaches fuel values paths before.machine.heap endpoints
  · cases decision with
    | closed _ actual =>
        exact SourceRefusedClassQuery.refutes_decision paths active values seeded ready available (endpoints_domain values paths endpoints)
          fields actual formulas solver ambient symbol terms accepted

end MicroCFTA.SourceCurrentMuEndpointQuery
