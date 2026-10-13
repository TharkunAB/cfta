import MicroCFTA.InternedFreeNameMuOrigins
import MicroCFTA.InternedSourceFreeNames

/-!
# Literal boundaries in the probes of actual stored recursive records

Historical origins provide both verified semantic tables before the
original depth probe. An old free-name bound on the actual stored body
therefore excludes fresh literal boundaries in both stored probes.
-/
namespace MicroCFTA.InternedStoredFreeNameBoundary
open Cache InternedConstructorTemplates InternedNestedConstruction InternedBoundaryAtoms
open InternedFreeNameMuOrigins
open InternedBinderProtocol (NodeKey)

/-- A stored source origin transfers the body's free-name bound to both original probes. -/
theorem origin_reference_absent [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (origin : Origin entry body depth ordinary) (cutoff : Nat)
    (old : ∀ identity, .interned identity ∈ body.free → identity < cutoff) :
    ∀ identity, cutoff ≤ identity →
      .ref (.interned identity) ∉ atoms depth ∧ .ref (.interned identity) ∉ atoms ordinary := by
  obtain ⟨expression, environment, before, afterDepth, beforeReserve, afterBody,
    normal, inputs, tables, depthDone, ordinaryDone, missing, entrySame, bodyDone⟩ := origin
  subst entry
  exact InternedSourceFreeNames.probes_reference_absent expression environment before afterDepth beforeReserve afterBody
    normal inputs tables.2 tables.1 depth ordinary body depthDone ordinaryDone missing bodyDone cutoff old

/-- Every complete Mu in a closed run has the literal-boundary implication, including a run that stops pending. -/
theorem closed_reference_absent [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (cutoff : Nat) (old : ∀ identity, .interned identity ∈ body.free → identity < cutoff) :
    ∀ identity, cutoff ≤ identity →
      .ref (.interned identity) ∉ atoms depth ∧ .ref (.interned identity) ∉ atoms ordinary :=
  origin_reference_absent entry body depth ordinary (closed_origins expression key entry body depth ordinary stored) cutoff old

end MicroCFTA.InternedStoredFreeNameBoundary
