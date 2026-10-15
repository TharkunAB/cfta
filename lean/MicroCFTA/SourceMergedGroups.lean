import MicroCFTA.SourceMergedEdges

/-!
# General successful group and root coverage

The four-row source threshold chooses the proved row branches. Executable
grouping supplies the complete symbol and arity classes. The final node
uses the exact rows returned by all ordered group computations.
-/
namespace MicroCFTA.SourceMergedGroups
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map small)
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)
open MergedPhysicalGroupEdges (SameKey)
open SourceMergedContracts SourceMergedColumns SourceMergedEdges

/-- Both successful source threshold branches cover all original group rows. -/
theorem group_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (fuel : Nat) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (law : RecurseLaw call holds ambient)
    (top : Guard) (topTrue : ∀ term, holds top term = true)
    (edges : List (EdgeValue Symbol Guard)) (keys : SameKey edges) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedWorker.group call clear fuel top edges before = .done results after) :
    Effect before after ∧ RowsPost holds ambient edges after results := by
  unfold SourceMergedWorker.group at done
  split at done
  · have checked := map_done (small call) (fun state edge => EdgeResident state edge ∧ ClosedValues edge.children)
      (fun state edge result => EdgePost holds ambient [edge] state result)
      (fun _ _ effects edge input => ⟨InternedEdgeResidency.edge_grows _ _ effects.1.growth edge input.1, input.2⟩)
      (fun _ _ effects _ _ post => post.grows effects) edges
      (fun edge _ state ready input result final done => small_done call holds ambient law edge state ready input.1 input.2 result final done)
      before semantic (fun edge member => ⟨resident edge member, closed edge member⟩) results after done
    refine ⟨checked.1,
      EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.resident)),
      EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.closed)), ?_⟩
    intro edge member term accepted
    obtain ⟨result, included, post⟩ := SymbolicSmartRows.all₂_child _ _ _ checked.2 edge member
    exact ⟨result, included, post.covers edge List.mem_cons_self term accepted⟩
  · cases edges with
    | nil => simp at *
    | cons first rest =>
        obtain ⟨result, final, made, returned⟩ := (bind_done _ _ results after).mp done
        have checked := large_done call clear fuel holds ambient clearTrue law top topTrue first rest keys before semantic resident closed result final made
        have parts := Result.done.inj returned
        cases parts.1; cases parts.2
        exact ⟨checked.1, (fun edge member => by rw [List.mem_singleton.mp member]; exact checked.2.resident),
          (fun edge member => by rw [List.mem_singleton.mp member]; exact checked.2.closed),
          fun edge member term accepted => ⟨result, List.mem_cons_self, checked.2.covers edge member term accepted⟩⟩

/-- A successful grouped root covers every original edge in the independent language. -/
theorem root_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (fuel : Nat) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (law : RecurseLaw call holds ambient)
    (top : Guard) (topTrue : ∀ term, holds top term = true)
    (edges : List (EdgeValue Symbol Guard)) (groups : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges groups) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.root call clear fuel top groups before = .done result after) :
    Effect before after ∧ Available after result ∧ result.free = [] ∧
      ∀ edge ∈ edges, ∀ term, EdgeMeaning (meaning holds ambient) holds edge term → meaning holds ambient result term := by
  obtain ⟨rows, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have checked := map_done (SourceMergedWorker.group call clear fuel top)
    (fun state edges => Edges state edges ∧ ClosedEdges edges) (fun state edges results => RowsPost holds ambient edges state results)
    (fun _ _ effects _ input => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effects.1.growth edge (input.1 edge member)), input.2⟩)
    (fun _ _ effects _ _ post => post.grows effects) groups
    (fun group member state ready input result final done => group_done call clear fuel holds ambient clearTrue law top topTrue
      group (grouping.keys edges groups group member) state ready input.1 input.2 result final done)
    before semantic (fun group member => ⟨(fun edge included => resident edge (original group member edge included)),
      (fun edge included => closed edge (original group member edge included))⟩) rows middle mapped
  have rowsResident : ∀ own ∈ rows, Edges middle own := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.resident))
  have rowsClosed : ∀ own ∈ rows, ClosedEdges own := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.closed))
  have flatResident : Edges middle rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowsResident own member edge included
  have flatClosed : ClosedEdges rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowsClosed own member edge included
  have constructed := SourceEqualityRequiredCache.node rows.flatten middle checked.1.2.ready flatResident flatClosed
  have parts := Result.done.inj made
  cases parts.1; cases parts.2
  refine ⟨checked.1.trans ⟨constructed.1, SourceEqualityRequiredSemanticCache.node _ middle checked.1.2 flatResident flatClosed⟩,
    constructed.2.1, constructed.2.2.1, ?_⟩
  intro edge member term accepted
  obtain ⟨group, member, included⟩ := List.mem_flatten.mp (grouping.partition.mem_iff.mpr member)
  obtain ⟨own, present, post⟩ := SymbolicSmartRows.all₂_child _ _ _ checked.2 group member
  obtain ⟨selected, included, run⟩ := post.covers edge included term accepted
  exact (MergedColdInterpretation.makeNode_exact middle checked.1.2.ready.semantic.1.normal.facts
    (meaning holds ambient) rows.flatten flatResident holds (InternedGuardedLanguage.laws holds ambient) term).mpr
    ⟨selected, List.mem_flatten.mpr ⟨own, present, included⟩, run⟩

end MicroCFTA.SourceMergedGroups
