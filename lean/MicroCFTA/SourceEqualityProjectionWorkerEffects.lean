import MicroCFTA.SourceEqualityProjectionWorkerPhysical

/-! Physical heap effects of actual recursive projection outcomes. -/
set_option autoImplicit false

namespace MicroCFTA.SourceEqualityProjectionWorkerPhysical
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (edge_grows resident_edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceEqualityRequiredWorker (Result work)
open SourceEqualityProjectionGraph (select select_member)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard A B : Type}

private def ValuePost (value : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  Available after value ∧ value.free = []
private def ValuesPost (values : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  Values after values ∧ ClosedValues values

private structure Verified (before : State Symbol Guard) (actual : Result Symbol Guard A)
    (post : A → State Symbol Guard → Prop) : Prop where
  semantic : SemanticHeap (reached actual)
  covered : Covered [] (reached actual)
  growth : Grows before (reached actual)
  history : Extends before.nodes.issued (reached actual).nodes.issued
  finished : ∀ value after, actual = .done value after → post value after

private theorem Verified.extend {before middle : State Symbol Guard} {actual : Result Symbol Guard A}
    {post : A → State Symbol Guard → Prop} (verified : Verified middle actual post)
    (growth : Grows before middle) (history : Extends before.nodes.issued middle.nodes.issued) :
    Verified before actual post :=
  ⟨verified.semantic, verified.covered, grows_trans growth verified.growth,
    extends_trans history verified.history, verified.finished⟩

private theorem pure_verified (before : State Symbol Guard) (semantic : SemanticHeap before)
    (covered : Covered [] before) (value : A) {post : A → State Symbol Guard → Prop}
    (valid : post value before) : Verified before (.done value before) post :=
  ⟨semantic, covered, grows_refl _, extends_refl _, by intro _ _ same; cases same; exact valid⟩

private theorem bind_verified {before : State Symbol Guard} {actual : Result Symbol Guard A}
    {post : A → State Symbol Guard → Prop} {next : A → State Symbol Guard → Result Symbol Guard B}
    {final : B → State Symbol Guard → Prop} (verified : Verified before actual post)
    (later : ∀ value after, Verified before (.done value after) post → Verified after (next value after) final) :
    Verified before (actual.bind next) final := by
  cases actual with
  | done value after => exact (later value after verified).extend verified.growth verified.history
  | pending key after | unresolved name after | exhausted limit after =>
      exact ⟨verified.semantic, verified.covered, verified.growth, verified.history,
        by intro _ _ same; cases same⟩

private theorem node_verified [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    Verified before (work (makeNode edges) before) ValuePost := by
  have facts := semantic.1.normal.facts
  have checked := InternedNestedFacts.node_verified edges before facts resident
  refine ⟨SourceRecursiveIntersectionSemanticHeap.node edges before semantic resident,
    InternedNestedCoverage.run_covered _ before facts.coherent.valid covered, checked.growth, checked.history, ?_⟩
  intro value after same
  cases same
  exact ⟨checked.result _ _ rfl, MergedColdReaderClosedInputs.makeNode_closed edges before facts resident closed⟩

private theorem exposure_heap (actual : Result Symbol Guard (List (EdgeValue Symbol Guard))) :
    (exposure actual).state = reached actual := by cases actual <;> rfl

private theorem readAll_effects [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Values before values) (closed : ClosedValues values) :
    Verified before (SourceEqualityProjectionWorker.readAll fuel values before)
      (fun edges after => Edges after edges ∧ ClosedEdges edges) := by
  have old := readAll_verified fuel values before semantic covered available closed
  refine ⟨by simpa only [exposure_heap] using old.semantic, by simpa only [exposure_heap] using old.covered,
    by simpa only [exposure_heap] using old.growth, by simpa only [exposure_heap] using old.history, ?_⟩
  intro edges after same
  have observed : exposure (SourceEqualityProjectionWorker.readAll fuel values before) = .done edges after := by
    rw [same]; rfl
  exact ⟨old.edges _ _ observed, old.closed _ _ observed⟩

private theorem union_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Values before values) (closed : ClosedValues values) :
    Verified before (SourceEqualityProjectionWorker.union fuel values before) ValuePost := by
  unfold SourceEqualityProjectionWorker.union
  apply bind_verified (readAll_effects fuel values before semantic covered available closed)
  intro edges after read
  exact node_verified edges after read.semantic read.covered (read.finished _ _ rfl).1 (read.finished _ _ rfl).2

private theorem head_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (query : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before query) (closed : query.free = []) :
    Verified before (SourceEqualityRequiredWorker.head fuel query before) ValuePost := by
  unfold SourceEqualityRequiredWorker.head
  generalize observed : MergedFreshOrdinaryExposure.nodeEdges fuel query before = actual
  have old : MergedFreshOrdinaryColdEffects.Verified before actual := by
    simpa only [observed] using MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel query before semantic covered available closed
  cases actual with
  | done edges after => exact (node_verified edges after old.semantic old.covered
      (old.edges _ _ rfl) (old.closed _ _ rfl)).extend old.growth old.history
  | pending key after | unresolved name after | exhausted after =>
      exact ⟨old.semantic, old.covered, old.growth, old.history, by intro _ _ same; cases same⟩

private theorem rows_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int)
    (smaller : ∀ (value : Value Symbol Guard) (before : State Symbol Guard), SemanticHeap before → Covered [] before → Available before value → value.free = [] →
      Verified before (SourceEqualityProjectionWorker.project fuel readFuel path value before) ValuePost)
    (index : Int) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before) (resident : Edges before edges) (closed : ClosedEdges edges) :
    Verified before (SourceEqualityProjectionWorker.rows
      (SourceEqualityProjectionWorker.project fuel readFuel path) index edges before) ValuesPost := by
  induction edges generalizing before with
  | nil => exact pure_verified before semantic covered [] ⟨by simp [Values], by simp [ClosedValues]⟩
  | cons edge edges ih =>
      have tailResident := fun row member => resident row (List.mem_cons_of_mem _ member)
      have tailClosed := fun row member => closed row (List.mem_cons_of_mem _ member)
      cases found : select edge.children index with
      | none =>
          simpa only [SourceEqualityProjectionWorker.rows, found] using ih before semantic covered tailResident tailClosed
      | some child =>
          rw [SourceEqualityProjectionWorker.rows, found]
          apply bind_verified (smaller child before semantic covered
            (semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child (select_member found))
            (closed edge List.mem_cons_self child (select_member found)))
          intro value middle one
          apply bind_verified (ih middle one.semantic one.covered
            (fun row member => edge_grows before middle one.growth row (tailResident row member)) tailClosed)
          intro values after tail
          have initial := one.finished _ _ rfl
          have final := tail.finished _ _ rfl
          refine pure_verified after tail.semantic tail.covered (value :: values) ⟨?_, ?_⟩
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact initial.1.grows middle after tail.growth tail.history
            · exact final.1 child member
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact initial.2
            · exact final.2 child member

private theorem project_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int)
    (query : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before query) (closed : query.free = []) :
    Verified before (SourceEqualityProjectionWorker.project fuel readFuel path query before) ValuePost := by
  induction fuel generalizing path query before with
  | zero => exact ⟨semantic, covered, grows_refl _, extends_refl _, by intro _ _ same; cases same⟩
  | succ fuel ih =>
      cases path with
      | nil => exact pure_verified before semantic covered query ⟨available, closed⟩
      | cons index path =>
          have expose (value : Value Symbol Guard) (resident : Available before value) (valueClosed : value.free = []) :
              Verified before ((SourceEqualityRequiredWorker.head readFuel value before).bind fun exposed after =>
                SourceEqualityProjectionWorker.project fuel readFuel (index :: path) exposed after) ValuePost := by
            apply bind_verified (head_verified readFuel value before semantic covered resident valueClosed)
            intro exposed after first
            exact ih (index :: path) exposed after first.semantic first.covered (first.finished _ _ rfl).1 (first.finished _ _ rfl).2
          cases query with
          | empty => exact pure_verified before semantic covered (Value.empty : Value Symbol Guard) ⟨empty_available before, rfl⟩
          | reference name => exact ⟨semantic, covered, grows_refl _, extends_refl _, by intro _ _ same; cases same⟩
          | node entry edges depth free =>
              rw [SourceEqualityProjectionWorker.project]
              apply bind_verified (rows_verified fuel readFuel path
                (fun value after sem cov avail cls => ih path value after sem cov avail cls) index edges before semantic covered
                (resident_edges before semantic.1.normal.facts.linked (.node entry edges depth free) available.resident)
                (MergedColdReaderClosed.node_children_closed before semantic.1.normal.facts entry edges depth free available closed))
              intro values after read
              exact union_verified readFuel values after read.semantic read.covered (read.finished _ _ rfl).1 (read.finished _ _ rfl).2
          | mu entry body depth free => exact expose (.mu entry body depth free) available closed
          | union entry members depth free => exact expose (.union entry members depth free) available closed

private theorem Verified.conclusion {before : State Symbol Guard} {actual : Result Symbol Guard (Value Symbol Guard)}
    (verified : Verified before actual ValuePost) :
    SemanticHeap (reached actual) ∧ Covered [] (reached actual) ∧ Grows before (reached actual) ∧
      Extends before.nodes.issued (reached actual).nodes.issued ∧
      match (generalizing := false) actual with
      | .done value after => Available after value ∧ value.free = []
      | .pending _ _ | .unresolved _ _ | .exhausted _ _ => True := by
  refine ⟨verified.semantic, verified.covered, verified.growth, verified.history, ?_⟩
  cases actual with
  | done value after => exact verified.finished _ _ rfl
  | pending _key _after => trivial
  | unresolved _name _after => trivial
  | exhausted _limit _after => trivial

open scoped Classical in
/-- Each actual projection outcome retains current heap resources and old records. -/
theorem project_effects (fuel readFuel : Nat) (path : List Int)
    (query : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before query) (closed : query.free = []) :
    let actual := SourceEqualityProjectionWorker.project fuel readFuel path query before
    let after := reached actual
    SemanticHeap after ∧ Covered [] after ∧ Grows before after ∧
      Extends before.nodes.issued after.nodes.issued ∧
      match actual with
      | .done value returned => Available returned value ∧ value.free = []
      | .pending _ _ | .unresolved _ _ | .exhausted _ _ => True := by
  exact (project_verified fuel readFuel path query before semantic covered available closed).conclusion

open scoped Classical in
/-- Forest projection retains each actual heap, including an absent signed child. -/
theorem forest_effects (fuel readFuel : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Values before values) (closed : ClosedValues values) :
    let actual := SourceEqualityProjectionWorker.forest fuel readFuel path values before
    let after := reached actual
    SemanticHeap after ∧ Covered [] after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
      match actual with
      | .done value returned => Available returned value ∧ value.free = []
      | .pending _ _ | .unresolved _ _ | .exhausted _ _ => True := by
  apply Verified.conclusion
  cases path with
  | nil => exact union_verified readFuel values before semantic covered available closed
  | cons index path =>
      cases found : select values index with
      | none => simpa only [SourceEqualityProjectionWorker.forest, found] using
          pure_verified before semantic covered (Value.empty : Value Symbol Guard) (post := ValuePost) ⟨empty_available before, rfl⟩
      | some value => simpa only [SourceEqualityProjectionWorker.forest, found] using
          project_verified fuel readFuel path value before semantic covered (available value (select_member found)) (closed value (select_member found))

end MicroCFTA.SourceEqualityProjectionWorkerPhysical
