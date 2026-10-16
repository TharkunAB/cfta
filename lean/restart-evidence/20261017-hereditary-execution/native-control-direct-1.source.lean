import MicroCFTA.SourceCurrentHereditaryNativeEffects
import MicroCFTA.SourceCurrentHereditaryNativeCache
import MicroCFTA.SourceCurrentAllocatedRecursivePrefixAdmission

/-!
# Local hereditary certificates for checked controls

A demanded edge retains its actual original rows before the checked prefix.
Each continuation receives its exact smaller result and causal Mu store.
Completed-cell laws concern only the queried operands and source bindings.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeControl
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentHereditaryNativeCode (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The two actual native controls retain the same local output contract. -/
def Certified (control : Control A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match control with
  | .code code => SourceCurrentHereditaryNativeEffects.Certified annotation source code state post
  | .edgeBody request next => Bindings annotation source request.domain.key ∧
      SourceCurrentHereditaryConstructors.Edge annotation request.left ∧
      SourceCurrentHereditaryConstructors.Edge annotation request.right ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → MuStored annotation after.heap →
        EdgeResident after.heap value → EdgeLaw annotation source request value →
        SourceCurrentHereditaryNativeEffects.Certified annotation source (next value) after post

/-- The actual returned state retains both local causal cache families. -/
structure Stored (state : Checked width) : Prop where
  /-- Constructor hits retain the relationship between stored bodies and their probes. -/
  constructors : MuStored annotation state.native.machine.heap
  /-- Returned native cells retain conditional laws for their original requests. -/
  native : SourceCurrentHereditaryNativeCache.Stored annotation source state.native

/-- An actual pure control supplies its local post at the same machine. -/
theorem pure_result (value : A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : Certified annotation source (.code (.pure value)) state post) : post state value := certificate

/-- Source sequencing retains local effects after each exact returned machine. -/
theorem certified_bind (control : Control A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (stored : MuStored annotation state.heap)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified annotation source control state intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      MuStored annotation after.heap → intermediate after value → Certified annotation source (.code (next value)) after post) :
    Certified annotation source (control.bind next) state post := by
  cases control with
  | code code => exact SourceCurrentHereditaryNativeEffects.certified_bind annotation source code next state valid stored intermediate post certificate continuation
  | edgeBody request resume =>
      refine ⟨certificate.1, certificate.2.1, certificate.2.2.1, ?_⟩
      intro value after afterValid growth afterStored resident law
      exact SourceCurrentHereditaryNativeEffects.certified_bind annotation source (resume value) next after afterValid afterStored
        intermediate post (certificate.2.2.2 value after afterValid growth afterStored resident law)
        (fun result final finalValid later finalStored middle => continuation result final finalValid (growth.trans later) finalStored middle)

/-- A node's annotated return supplies its conditional cache law for any later valid input test. -/
theorem node_law (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (annotated : Annotated annotation value) : NodeLaw annotation source request value := fun _ _ _ => annotated

/-- A row's annotated return supplies its conditional cache law for its complete original request. -/
theorem edge_law (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (annotated : SourceCurrentHereditaryConstructors.Edge annotation value) : EdgeLaw annotation source request value := fun _ _ _ => annotated

end MicroCFTA.SourceCurrentHereditaryNativeControl
