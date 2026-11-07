import MicroCFTA.SourceSynthesisUniverseProbeChildren

/-!
# Physical probe replay from actual universe product rows

The actual product row retains the transformed original children.
Replacing its diagonal cutoff therefore gives the original probe request.
Parallel ordered readbacks retain the same complete probe rows.
-/
namespace MicroCFTA.SourceSynthesisUniverseProductProbeRows
open Cache Language InternedConstructorTemplates
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionControl (pair)
open SourceSynthesisUniverseRowTransform (Readback)

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual product readback transfers the original pure probe edge replay. -/
theorem row_replay (top : Guard) (uId : Nat) (probe : Reference) (marker : Value Symbol Guard)
    (original product target : EdgeValue Symbol Guard) (current : InternedConstructorTemplates.State Symbol Guard)
    (closed : marker.free = [])
    (kinds : ∀ child ∈ original.children, child = marker ∨ child = .reference (.interned uId))
    (readback : Readback top uId original product)
    (replayed : run (makeEdge original.entry.key.symbol top
      (original.children.map (input (replacement (.interned uId) (.reference probe))))) current =
        (target, current)) :
    run (makeEdge product.entry.key.symbol top
      (product.children.map (input
        (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe))))) current =
          (target, current) := by
  have projected := congrArg EdgeKey.symbol readback.2
  have symbol : product.entry.key.symbol = original.entry.key.symbol := projected
  rw [symbol, readback.1, SourceSynthesisUniverseProbeChildren.makeEdge_compose top uId probe marker original closed kinds]
  exact replayed

/-- Parallel source-ordered readbacks transfer every actual probe edge replay. -/
theorem rows_replay (top : Guard) (uId : Nat) (probe : Reference) (marker : Value Symbol Guard)
    (originals products targets : List (EdgeValue Symbol Guard))
    (current : InternedConstructorTemplates.State Symbol Guard) (closed : marker.free = [])
    (kinds : ∀ original ∈ originals, ∀ child ∈ original.children,
      child = marker ∨ child = .reference (.interned uId))
    (readback : All₂ (Readback top uId) originals products)
    (replayed : All₂ (fun original target =>
      run (makeEdge original.entry.key.symbol top
        (original.children.map (input (replacement (.interned uId) (.reference probe))))) current =
          (target, current)) originals targets) :
    All₂ (fun product target =>
      run (makeEdge product.entry.key.symbol top
        (product.children.map (input
          (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe))))) current =
            (target, current)) products targets := by
  revert kinds replayed
  induction readback generalizing targets with
  | nil => intro _ replayed; cases replayed; exact .nil
  | @cons original product originals products own rest ih =>
      intro kinds replayed
      cases replayed with
      | @cons _ target _ targets first tail =>
          exact .cons
            (row_replay top uId probe marker original product target current closed
              (kinds original List.mem_cons_self) own first)
            (ih targets (fun original member => kinds original (List.mem_cons_of_mem _ member)) tail)

end MicroCFTA.SourceSynthesisUniverseProductProbeRows
