import MicroCFTA.SourceEqualityProjectionWorkerEffects

set_option autoImplicit false
/- Physical effects of the actual required-path worker. -/
namespace MicroCFTA.SourceEqualityProjectionWorkerPhysical
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (edge_grows resident_edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceEqualityRequiredWorker (Result work)
open SourceEqualityNeeded (Needed fits)
open scoped Classical
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard A B : Type}

private def ValuePost (Guard : Type) (value : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  Available after value ∧ value.free = []
private def EdgePost (Guard : Type) (edge : EdgeValue Symbol Guard) (after : State Symbol Guard) : Prop :=
  Edges after [edge] ∧ ClosedEdges [edge]
private def ListPost (post : A → State Symbol Guard → Prop) (values : List A) (after : State Symbol Guard) : Prop :=
  ∀ value ∈ values, post value after
private structure Verified (before : State Symbol Guard) (actual : Result Symbol Guard A)
    (post : A → State Symbol Guard → Prop) : Prop where
  semantic : SemanticHeap (reached actual)
  covered : Covered [] (reached actual)
  growth : Grows before (reached actual)
  history : Extends before.nodes.issued (reached actual).nodes.issued
  finished : ∀ value after, actual = .done value after → post value after

private theorem Verified.extend {before middle : State Symbol Guard} {actual : Result Symbol Guard A}
    {post : A → State Symbol Guard → Prop} (v : Verified middle actual post)
    (g : Grows before middle) (h : Extends before.nodes.issued middle.nodes.issued) : Verified before actual post :=
  ⟨v.semantic, v.covered, grows_trans g v.growth, extends_trans h v.history, v.finished⟩
private theorem pure_verified (before : State Symbol Guard) (sem : SemanticHeap before) (cov : Covered [] before)
    (value : A) {post : A → State Symbol Guard → Prop} (valid : post value before) : Verified before (.done value before) post :=
  ⟨sem, cov, grows_refl _, extends_refl _, by intro _ _ same; cases same; exact valid⟩
private theorem bind_verified {before : State Symbol Guard} {actual : Result Symbol Guard A}
    {post : A → State Symbol Guard → Prop} {next : A → State Symbol Guard → Result Symbol Guard B}
    {final : B → State Symbol Guard → Prop} (v : Verified before actual post)
    (later : ∀ value after, Verified before (.done value after) post → Verified after (next value after) final) :
    Verified before (actual.bind next) final := by
  cases actual with
  | done value after => exact (later value after v).extend v.growth v.history
  | pending key after | unresolved name after | exhausted limit after =>
      exact ⟨v.semantic, v.covered, v.growth, v.history, by intro _ _ same; cases same⟩
private theorem value_carry (before after : State Symbol Guard) (g : Grows before after)
    (h : Extends before.nodes.issued after.nodes.issued) (value : Value Symbol Guard) (p : ValuePost Guard value before) :
    ValuePost Guard value after := ⟨p.1.grows before after g h, p.2⟩
private theorem edge_carry (before after : State Symbol Guard) (g : Grows before after)
    (_h : Extends before.nodes.issued after.nodes.issued) (edge : EdgeValue Symbol Guard) (p : EdgePost Guard edge before) :
    EdgePost Guard edge after := ⟨fun row member => edge_grows before after g row (p.1 row member), p.2⟩
private theorem cons_verified {post : A → State Symbol Guard → Prop}
    (carry : ∀ before after, Grows before after → Extends before.nodes.issued after.nodes.issued → ∀ value, post value before → post value after)
    (value : A) (before : State Symbol Guard) (one : post value before) {actual : Result Symbol Guard (List A)}
    (tail : Verified before actual (ListPost post)) :
    Verified before (actual.bind fun values after => .done (value :: values) after) (ListPost post) := by
  apply bind_verified tail
  intro values after part
  refine pure_verified after part.semantic part.covered (value :: values) ?_
  intro child member
  rcases List.mem_cons.mp member with same | member
  · subst child
    exact carry before after part.growth part.history value one
  · exact part.finished _ _ rfl child member

private theorem node_verified (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (sem : SemanticHeap before) (cov : Covered [] before) (resident : Edges before edges) (closed : ClosedEdges edges) :
    Verified before (work (makeNode edges) before) (ValuePost Guard) := by
  have facts := sem.1.normal.facts
  have checked := InternedNestedFacts.node_verified edges before facts resident
  refine ⟨SourceRecursiveIntersectionSemanticHeap.node edges before sem resident,
    InternedNestedCoverage.run_covered _ before facts.coherent.valid cov, checked.growth, checked.history, ?_⟩
  intro value after same
  cases same
  exact ⟨checked.result _ _ rfl, MergedColdReaderClosedInputs.makeNode_closed edges before facts resident closed⟩
private theorem edge_verified (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (sem : SemanticHeap before) (cov : Covered [] before)
    (safe : ListPost (ValuePost Guard) values before) :
    Verified before (work (makeEdge symbol guard values) before) (EdgePost Guard) := by
  have facts := sem.1.normal.facts
  have available : Values before values := fun value member => (safe value member).1
  have checked := InternedNestedFacts.edge_verified symbol guard values before facts available
  refine ⟨SourceRecursiveIntersectionSemanticHeap.edge symbol guard values before sem available,
    InternedNestedCoverage.run_covered _ before facts.coherent.valid cov, checked.growth, checked.history, ?_⟩
  intro value after same
  cases same
  exact ⟨by simpa [Edges] using checked.result _ _ rfl,
    by simpa [ClosedEdges, InternedShallowValues.makeEdge_children symbol guard values before facts.coherent facts.cached available]
      using (show ClosedValues values from fun child member => (safe child member).2)⟩

private theorem head_eq_forest (fuel : Nat) (query : Value Symbol Guard) (before : State Symbol Guard) :
    SourceEqualityRequiredWorker.head fuel query before = SourceEqualityProjectionWorker.forest 0 fuel [] [query] before := by
  unfold SourceEqualityRequiredWorker.head SourceEqualityProjectionWorker.forest SourceEqualityProjectionWorker.union
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel query before with
  | done edges after => simp only [SourceEqualityProjectionWorker.readAll, exposed, Result.bind, List.append_nil]
  | pending key after | unresolved name after | exhausted after =>
      simp only [SourceEqualityProjectionWorker.readAll, exposed, Result.bind]
private theorem head_verified (fuel : Nat) (query : Value Symbol Guard) (before : State Symbol Guard)
    (sem : SemanticHeap before) (cov : Covered [] before) (available : Available before query) (closed : query.free = []) :
    Verified before (SourceEqualityRequiredWorker.head fuel query before) (ValuePost Guard) := by
  have actual := forest_effects 0 fuel [] [query] before sem cov (by simpa [Values] using available) (by simpa [ClosedValues] using closed)
  dsimp only at actual
  rw [← head_eq_forest fuel query before] at actual
  refine ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1, ?_⟩
  intro value after same
  simpa only [same, ValuePost] using actual.2.2.2.2

private theorem children_verified (fuel readFuel : Nat)
    (smaller : ∀ needed value before, SemanticHeap before → Covered [] before → Available before value → value.free = [] →
      Verified before (SourceEqualityRequiredWorker.require fuel readFuel needed value before) (ValuePost Guard))
    (entries : List (Int × Needed)) (index : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (sem : SemanticHeap before) (cov : Covered [] before) (safe : ListPost (ValuePost Guard) values before) :
    Verified before (SourceEqualityRequiredWorker.children (SourceEqualityRequiredWorker.require fuel readFuel)
      entries index values before) (ListPost (ValuePost Guard)) := by
  induction values generalizing index before with
  | nil => exact pure_verified before sem cov [] (by intro value member; cases member)
  | cons value values ih =>
      have tail := fun child member => safe child (List.mem_cons_of_mem _ member)
      cases selected : SourceEqualityNeededMap.lookup (index : Int) entries with
      | none => simpa only [SourceEqualityRequiredWorker.children, selected] using
          cons_verified value_carry value before (safe value List.mem_cons_self) (ih (index + 1) before sem cov tail)
      | some needed =>
          rw [SourceEqualityRequiredWorker.children, selected]
          apply bind_verified (smaller needed value before sem cov (safe value List.mem_cons_self).1 (safe value List.mem_cons_self).2)
          intro result middle first
          exact cons_verified value_carry result middle (first.finished _ _ rfl)
            (ih (index + 1) middle first.semantic first.covered
              (fun child member => value_carry before middle first.growth first.history child (tail child member)))

private theorem rows_verified (fuel readFuel : Nat)
    (smaller : ∀ needed value before, SemanticHeap before → Covered [] before → Available before value → value.free = [] →
      Verified before (SourceEqualityRequiredWorker.require fuel readFuel needed value before) (ValuePost Guard))
    (entries : List (Int × Needed)) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (sem : SemanticHeap before) (cov : Covered [] before) (safe : ListPost (EdgePost Guard) edges before) :
    Verified before (SourceEqualityRequiredWorker.rows (SourceEqualityRequiredWorker.require fuel readFuel)
      entries edges before) (ListPost (EdgePost Guard)) := by
  induction edges generalizing before with
  | nil => exact pure_verified before sem cov [] (by intro edge member; cases member)
  | cons edge edges ih =>
      have tail := fun row member => safe row (List.mem_cons_of_mem _ member)
      have resident := (safe edge List.mem_cons_self).1 edge List.mem_cons_self
      have closed := (safe edge List.mem_cons_self).2 edge List.mem_cons_self
      by_cases matching : fits (.node entries) edge.children.length = true
      · simp only [SourceEqualityRequiredWorker.rows, matching, ite_true]
        apply bind_verified (children_verified fuel readFuel smaller entries 0 edge.children before sem cov
          (fun child member => ⟨sem.1.normal.facts.cached.edges edge.entry.key edge resident child member, closed child member⟩))
        intro values middle children
        apply bind_verified (edge_verified edge.entry.key.symbol edge.entry.key.constraint values middle
          children.semantic children.covered (children.finished _ _ rfl))
        intro result afterEdge rebuilt
        exact cons_verified edge_carry result afterEdge (rebuilt.finished _ _ rfl)
          (ih afterEdge rebuilt.semantic rebuilt.covered (fun row member => edge_carry before afterEdge
            (grows_trans children.growth rebuilt.growth) (extends_trans children.history rebuilt.history) row (tail row member)))
      · simpa only [SourceEqualityRequiredWorker.rows, matching, Bool.false_eq_true, ↓reduceIte] using ih before sem cov tail

private theorem require_verified (fuel readFuel : Nat) (needed : Needed) (query : Value Symbol Guard)
    (before : State Symbol Guard) (sem : SemanticHeap before) (cov : Covered [] before)
    (available : Available before query) (closed : query.free = []) :
    Verified before (SourceEqualityRequiredWorker.require fuel readFuel needed query before) (ValuePost Guard) := by
  induction fuel generalizing needed query before with
  | zero => exact ⟨sem, cov, grows_refl _, extends_refl _, by intro _ _ same; cases same⟩
  | succ fuel ih =>
      cases needed with
      | node entries =>
          by_cases emptyNeeded : entries.isEmpty = true
          · simpa only [SourceEqualityRequiredWorker.require, emptyNeeded, ite_true] using
              pure_verified before sem cov query (post := ValuePost Guard) ⟨available, closed⟩
          · have expose (value : Value Symbol Guard) (resident : Available before value) (valueClosed : value.free = []) :
                Verified before ((SourceEqualityRequiredWorker.head readFuel value before).bind fun exposed after =>
                  SourceEqualityRequiredWorker.require fuel readFuel (.node entries) exposed after) (ValuePost Guard) := by
              apply bind_verified (head_verified readFuel value before sem cov resident valueClosed)
              intro exposed after head
              exact ih (.node entries) exposed after head.semantic head.covered (head.finished _ _ rfl).1 (head.finished _ _ rfl).2
            cases query with
            | empty => simpa only [SourceEqualityRequiredWorker.require, emptyNeeded, Bool.false_eq_true, ↓reduceIte] using
                pure_verified before sem cov .empty (post := ValuePost Guard) ⟨empty_available before, rfl⟩
            | reference name =>
                simp only [SourceEqualityRequiredWorker.require, emptyNeeded, Bool.false_eq_true, ↓reduceIte]
                exact ⟨sem, cov, grows_refl _, extends_refl _, by intro _ _ same; cases same⟩
            | node entry edges depth free =>
                simp only [SourceEqualityRequiredWorker.require, emptyNeeded, Bool.false_eq_true, ↓reduceIte]
                have resident := resident_edges before sem.1.normal.facts.linked (.node entry edges depth free) available.resident
                have closedRows := MergedColdReaderClosed.node_children_closed before sem.1.normal.facts entry edges depth free available closed
                apply bind_verified (rows_verified fuel readFuel ih entries edges before sem cov
                  (fun row member => ⟨by simpa [Edges] using resident row member, by simpa [ClosedEdges] using closedRows row member⟩))
                intro rebuilt after rows
                exact node_verified rebuilt after rows.semantic rows.covered
                  (fun row member => (rows.finished _ _ rfl row member).1 row List.mem_cons_self)
                  (fun row member => (rows.finished _ _ rfl row member).2 row List.mem_cons_self)
            | mu entry body depth free => simpa only [SourceEqualityRequiredWorker.require, emptyNeeded, Bool.false_eq_true, ↓reduceIte] using expose (.mu entry body depth free) available closed
            | union entry members depth free => simpa only [SourceEqualityRequiredWorker.require, emptyNeeded, Bool.false_eq_true, ↓reduceIte] using expose (.union entry members depth free) available closed

/-- Every actual required-path outcome retains its physical heap resources. -/
theorem require_effects (fuel readFuel : Nat) (needed : Needed) (query : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (covered : Covered [] before)
    (available : Available before query) (closed : query.free = []) :
    let actual := SourceEqualityRequiredWorker.require fuel readFuel needed query before
    let after := reached actual
    SemanticHeap after ∧ Covered [] after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
      match actual with
      | .done value returned => Available returned value ∧ value.free = []
      | .pending _ _ | .unresolved _ _ | .exhausted _ _ => True := by
  have v := require_verified fuel readFuel needed query before semantic covered available closed
  refine ⟨v.semantic, v.covered, v.growth, v.history, ?_⟩
  match (generalizing := false) h : SourceEqualityRequiredWorker.require fuel readFuel needed query before with
  | .done value after => exact v.finished _ _ h
  | .pending .. | .unresolved .. | .exhausted .. => trivial

end MicroCFTA.SourceEqualityProjectionWorkerPhysical
