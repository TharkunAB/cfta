import MicroCFTA.SourcePhysicalRecursiveRowsLanguage

/-!
# Shared cyclic rows from the actual one-knot exposure

The Mu identity is retained as the recursive child state. Its exposed rows
are copied from the actual completed ordinary result. The resulting shared
traversal has one reachable identity and the independent chain language.
-/
namespace MicroCFTA.SourcePhysicalRecursiveRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency Language

/-- The shared adapter retains ordinary, Mu, and union identities without an EmptyState collision. -/
def reference : Value Symbol Unit → SourceInternedRows.Ref
  | .node entry .. | .mu entry .. | .union entry .. => some entry.identity
  | _ => none

/-- Actual exposed edge payloads retain their ordered recursive child identities. -/
def exposure (edge : EdgeValue Symbol Unit) : SourceInternedRows.Row Symbol Unit :=
  ⟨edge.entry.key.symbol, edge.children.map reference, edge.entry.key.constraint⟩

/-- Restrict this one-knot source snapshot to its single reachable identity. -/
def heap (identity : Nat) (exposed : List (SourceInternedRows.Row Symbol Unit)) : SourceInternedRows.Heap Symbol Unit :=
  fun query => if query = identity then exposed else []

/-- Membership describes the base and unary self row without imposing a different order. -/
def LoopRows (identity : Nat) (base step : Symbol) (rows : List (SourceInternedRows.Row Symbol Unit)) : Prop :=
  ∀ row, row ∈ rows ↔ row = ⟨base, [], ()⟩ ∨ row = ⟨step, [some identity], ()⟩

/-- Derived physical readback supplies the exact shared self-loop rows. -/
theorem exposed_loop (root result : Value Symbol Unit) (identity : Nat) (base step : Symbol)
    (same : reference root = some identity) (exposed : Exposed root result base step) :
    LoopRows identity base step ((nodeEdges result).map exposure) := by
  obtain ⟨first, second, firstSymbol, firstChildren, secondSymbol, secondChildren, _, members⟩ := exposed.rows
  have firstRow : exposure first = ⟨base, [], ()⟩ := by
    simp [exposure, firstSymbol, firstChildren]
  have secondRow : exposure second = ⟨step, [some identity], ()⟩ := by
    simp [exposure, secondSymbol, secondChildren, same]
  intro row
  constructor
  · intro member
    obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
    rcases (members edge).mp edgeIn with rfl | rfl
    · exact Or.inl firstRow
    · exact Or.inr secondRow
  · intro member
    rcases member with rfl | rfl
    · exact List.mem_map.mpr ⟨first, (members first).mpr (Or.inl rfl), firstRow⟩
    · exact List.mem_map.mpr ⟨second, (members second).mpr (Or.inr rfl), secondRow⟩

/-- The concrete exposed loop needs exactly one identity in its finite traversal domain. -/
theorem loop_closed (identity : Nat) (base step : Symbol) (rows : List (SourceInternedRows.Row Symbol Unit))
    (loop : LoopRows identity base step rows) : SourceInternedRows.ClosedDomain (heap identity rows) [identity] := by
  intro current member child inside
  rw [List.mem_singleton.mp member] at inside
  have pending := (SourceInternedRows.mem_successors (heap identity rows) identity child).mp inside
  obtain ⟨row, member, childIn⟩ := List.mem_flatMap.mp pending
  have present : row ∈ rows := by simpa [heap] using member
  rcases (loop row).mp present with rfl | rfl
  · cases childIn
  · simpa using childIn

/-- The shared loop has precisely the same finite one-step equation as the actual Mu. -/
theorem loop_equation (identity : Nat) (base step : Symbol) (rows : List (SourceInternedRows.Row Symbol Unit))
    (loop : LoopRows identity base step rows) (term : Term Symbol) :
    Language.Accepts (SourceInternedRows.graph (heap identity rows) (fun _ _ => true)) (.interned identity) term ↔
      term = .node base [] ∨ ∃ child, term = .node step [child] ∧
        Language.Accepts (SourceInternedRows.graph (heap identity rows) (fun _ _ => true)) (.interned identity) child := by
  constructor
  · intro accepted
    cases accepted with
    | node edge terms member runs guard =>
        obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
        have rowIn : row ∈ rows := by simpa [heap] using present
        rcases (loop row).mp rowIn with rfl | rfl
        · cases runs
          exact Or.inl rfl
        · cases runs with
          | cons child rest => cases rest; exact Or.inr ⟨_, rfl, child⟩
  · intro accepted
    rcases accepted with rfl | ⟨child, rfl, accepted⟩
    · exact .node ⟨base, [], fun _ => true⟩ []
        (List.mem_map.mpr ⟨⟨base, [], ()⟩, by simpa [heap] using (loop ⟨base, [], ()⟩).mpr (Or.inl rfl), rfl⟩) .nil rfl
    · exact .node ⟨step, [.interned identity], fun _ => true⟩ [child]
        (List.mem_map.mpr ⟨⟨step, [some identity], ()⟩,
          by simpa [heap] using (loop ⟨step, [some identity], ()⟩).mpr (Or.inr rfl), rfl⟩) (.cons accepted .nil) rfl

/-- Every finite shared-loop run is an independently specified chain. -/
theorem loop_sound (identity : Nat) (base step : Symbol) (rows : List (SourceInternedRows.Row Symbol Unit))
    (loop : LoopRows identity base step rows) (term : Term Symbol)
    (accepted : Language.Accepts (SourceInternedRows.graph (heap identity rows) (fun _ _ => true)) (.interned identity) term) :
    Chain base step term := by
  rcases (loop_equation identity base step rows loop term).mp accepted with rfl | ⟨child, rfl, childAccepted⟩
  · exact .base
  · exact .step (loop_sound identity base step rows loop child childAccepted)
termination_by term.height
decreasing_by subst term; simp [Term.height]

/-- Every independently specified chain has a finite shared-loop run. -/
theorem loop_complete (identity : Nat) (base step : Symbol) (rows : List (SourceInternedRows.Row Symbol Unit))
    (loop : LoopRows identity base step rows) (term : Term Symbol) (chain : Chain base step term) :
    Language.Accepts (SourceInternedRows.graph (heap identity rows) (fun _ _ => true)) (.interned identity) term := by
  induction chain with
  | base => exact (loop_equation identity base step rows loop _).mpr (Or.inl rfl)
  | step child ih => exact (loop_equation identity base step rows loop _).mpr (Or.inr ⟨_, rfl, ih⟩)

/-- Current physical unfolding yields finite exact shared rows for the recursive language. -/
theorem shared_exposure [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary : Value Symbol Unit)
    (state : State Symbol Unit) (facts : Facts state)
    (available : Available state (knot entry bodyEntry base step depth ordinary)) :
    ∃ result after fuel raw,
      InternedFreshOrdinaryStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) state =
        .done result after ∧ Facts after ∧ Available after result ∧
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap entry.identity ((nodeEdges result).map exposure))
        larger (some entry.identity) = some raw) ∧
      (∀ term, Language.Accepts (SourceRowsMinimumAdapter.automaton raw) (.interned entry.identity) term ↔
        Physical state (knot entry bodyEntry base step depth ordinary) term) := by
  obtain ⟨result, after, currentDone, oldDone, afterFacts, growth, history, resultAvailable, rootAvailable, exposed⟩ :=
    unfold_complete entry bodyEntry base step depth ordinary state facts available
  have loop := exposed_loop _ result entry.identity base.key.symbol step.key.symbol (by rfl) exposed
  obtain ⟨fuel, raw, done⟩ := SourceInternedRows.toRows_finite (heap entry.identity ((nodeEdges result).map exposure))
    [entry.identity] (loop_closed _ _ _ _ loop) (some entry.identity) (by intro identity same; cases same; simp)
  refine ⟨result, after, fuel, raw, currentDone, afterFacts, resultAvailable, done, ?_⟩
  intro term
  exact (SourceRowsMinimumPublic.root_language _ fuel (some entry.identity) raw (done fuel (Nat.le_refl _)) term).trans
    ((Iff.intro (loop_sound _ _ _ _ loop term) (loop_complete _ _ _ _ loop term)).trans
      (Iff.intro (accepts_chain _ _ _ _ _ _ _ _ _ oldDone exposed term)
        (chain_accepts _ _ _ _ _ _ _ _ _ oldDone exposed term)).symm)

end MicroCFTA.SourcePhysicalRecursiveRows
