import MicroCFTA.SourceCurrentAllocatedPrimaryReads

/-!
# Validity of the supplied current gate reads

Each proof follows its actual memo receipt. Predicate calls and unfolding
calls determine the tables used by its recursive suffix. The proof does
not identify different schedules from equality of their returned heaps.
-/
namespace MicroCFTA.SourceCurrentAllocatedGateReadValidity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open EqualityNormalize
open EndpointMemoGateTrace (Memos Valid Keeps pure_keeps prepend_keeps)
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The supplied predicate and unfolding calls derive their exact intermediate validity. -/
private theorem unfold_step
    {entry : Interned InternedBinderProtocol.NodeKey} {body depth ordinary : Value Symbol Guard}
    {before after : State Symbol Guard} {next : Value Symbol Guard}
    {memos : Memos} {middlePredicate : SourceUnconstrainedMemo.Memo}
    {middleUnfolding : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard}
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) before = .done next after)
    (predicate : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate = (true, middlePredicate))
    (unfolding : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memos.unfolding before =
      .done (next, middleUnfolding) after)
    (ready : Ready before) (available : Available before (.mu entry body depth ordinary)) (valid : Valid before memos) :
    Keeps before after ⟨middleUnfolding, {memos.query with predicate := middlePredicate}⟩ ∧ Available after next := by
  have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available
    memos.query.predicate valid.query.predicate
  have predicateValid : SourceUnconstrainedMemo.Correct before middlePredicate := by
    simpa only [predicate] using checked.2
  let middleQuery : SourceEndpointMemo.Memos := {memos.query with predicate := middlePredicate}
  have queryValid : SourceEndpointMemo.Valid before middleQuery := ⟨valid.query.descendants, predicateValid⟩
  obtain ⟨finished, saved, memoActual, readback, correct, growth, history⟩ :=
    InternedFreshOrdinaryUnfoldMemo.run_complete (ready.node _ available) memos.unfolding valid.unfolding
  have fields := Outcome.done.inj (readback.symm.trans actual)
  have valueEqual := fields.1
  have stateEqual := fields.2
  have normalized : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memos.unfolding before =
      .done (next, saved) after := by
    simpa only [Ready.node, valueEqual, stateEqual] using memoActual
  have same : saved = middleUnfolding := congrArg Prod.snd (Outcome.done.inj (normalized.symm.trans unfolding)).1
  subst saved
  have nextReady := stateEqual ▸ node_ready finished
  have nextAvailable := stateEqual ▸ (valueEqual ▸ finished.available)
  have nextCorrect := stateEqual ▸ correct
  have nextQuery := stateEqual ▸ SourceEndpointMemo.grows _ _ growth history middleQuery queryValid
  exact ⟨⟨nextReady, ⟨nextCorrect, nextQuery⟩,
    by simpa only [Ready.node, stateEqual] using growth,
    by simpa only [Ready.node, stateEqual] using history⟩, nextAvailable⟩

/-- Supplied primary node reads derive validity of their own returned tables. -/
theorem primary_node
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    {trace : EndpointStatefulGateTrace.NodeTrace source reaches path value before answer after}
    {memos saved : Memos} (reads : SourceCurrentAllocatedPrimaryReads.NodeReads trace memos saved)
    (ready : Ready before) (available : Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  revert ready available valid
  induction reads using SourceCurrentAllocatedPrimaryReads.NodeReads.rec
      (motive_2 := fun {values _index _path before _answer after} _ memos saved _ =>
        Ready before → (∀ value ∈ values, Available before value) → Valid before memos → Keeps before after saved)
      (motive_3 := fun {_index _path edges before _answer after} _ memos saved _ =>
        Ready before → (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) →
          Valid before memos → Keeps before after saved) with
  | empty | reference | union | finite | endpoint_open =>
      intro ready available valid
      exact pure_keeps _ _ ready valid
  | endpoint_closed slow closed actual =>
      intro ready available valid
      have checked := SourceEndpointMemoCorrect.run_checked _ _ ready.1.normal.facts.coherent available _ valid.query
      refine pure_keeps _ _ ready ⟨valid.unfolding, ?_⟩
      have queryValid := checked.valid
      change SourceEndpointMemo.Valid _ (SourceEndpointMemo.run _ _).2 at queryValid
      rw [actual] at queryValid
      exact queryValid
  | branches slow trace ih =>
      intro ready available valid
      exact ih ready (fun value member => available.children value member) valid
  | constrained blocked actual =>
      intro ready available valid
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available _ valid.query.predicate
      exact pure_keeps _ _ ready ⟨valid.unfolding, valid.query.descendants, by simpa only [actual] using checked.2⟩
  | closed plain closed actual =>
      intro ready available valid
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available _ valid.query.predicate
      exact pure_keeps _ _ ready ⟨valid.unfolding, valid.query.descendants, by simpa only [actual] using checked.2⟩
  | unfold plain opened actual predicate unfolding trace ih =>
      intro ready available valid
      have first := unfold_step actual predicate unfolding ready available valid
      exact prepend_keeps first.1 (ih first.1.ready first.2 first.1.valid)
  | missing absent ready available valid =>
      exact pure_keeps _ _ ready valid
  | present found trace ih ready available valid =>
      exact ih ready (available _ (List.mem_of_getElem? found)) valid
  | nil ready available valid =>
      exact pure_keeps _ _ ready valid
  | stop head ih ready available valid =>
      exact ih ready (fun value member => available value (by simp [member])) valid
  | next head tail headIH tailIH ready available valid =>
      have first := headIH ready (fun value member => available value (by simp [member])) valid
      exact prepend_keeps first (tailIH first.ready
        (fun value member => (available value (by simp [member])).grows _ _ first.growth first.history) first.valid)

/-- Supplied primary child reads preserve their exact returned tables. -/
theorem primary_child
    {values : List (Value Symbol Guard)} {index : Nat} {path : Path}
    {before after : State Symbol Guard} {answer : Bool}
    {trace : EndpointStatefulGateTrace.ChildTrace source reaches values index path before answer after}
    {memos saved : Memos} (reads : SourceCurrentAllocatedPrimaryReads.ChildReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ values, Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  cases reads with
  | missing => exact pure_keeps _ _ ready valid
  | present found called => exact primary_node called ready (available _ (List.mem_of_getElem? found)) valid

/-- Supplied primary row reads thread each actual returned heap and memo bundle. -/
theorem primary_edges
    {index : Nat} {path : Path} {edges : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {answer : Bool}
    {trace : EndpointStatefulGateTrace.EdgesTrace source reaches index path edges before answer after}
    {memos saved : Memos} (reads : SourceCurrentAllocatedPrimaryReads.EdgesReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available before value)
    (valid : Valid before memos) : Keeps before after saved := by
  revert ready available valid
  induction reads using SourceCurrentAllocatedPrimaryReads.EdgesReads.rec
      (motive_1 := fun {_path _value _before _answer _after} _ _ _ _ => True)
      (motive_2 := fun {_values _index _path _before _answer _after} _ _ _ _ => True) with
  | empty | reference | union | finite | endpoint_open | endpoint_closed | branches | constrained | closed | unfold | missing | present => trivial
  | nil => intro ready available valid; exact pure_keeps _ _ ready valid
  | stop head _ =>
      intro ready available valid
      exact primary_child head ready (fun value member => available value (by simp [member])) valid
  | next head tail _ ih =>
      intro ready available valid
      have first := primary_child head ready (fun value member => available value (by simp [member])) valid
      exact prepend_keeps first (ih first.ready
        (fun value member => (available value (by simp [member])).grows _ _ first.growth first.history) first.valid)

/-- Supplied primary path reads derive validity without choosing a different schedule. -/
theorem primary_path
    {values : List (Value Symbol Guard)} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    {trace : EndpointStatefulGateTrace.PathTrace source reaches values path before answer after}
    {memos saved : Memos} (reads : SourceCurrentAllocatedPrimaryReads.PathReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ values, Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  cases reads with
  | empty => exact pure_keeps _ _ ready valid
  | child called => exact primary_child called ready available valid

/-- Supplied primary class reads retain validity across the exact visited path prefix. -/
theorem primary_class
    {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
    {trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths before answer after}
    {memos saved : Memos} (reads : SourceCurrentAllocatedPrimaryReads.ClassReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ values, Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  revert ready available valid
  induction reads with
  | nil => intro ready available valid; exact pure_keeps _ _ ready valid
  | stop head => intro ready available valid; exact primary_path head ready available valid
  | next head tail ih =>
      intro ready available valid
      have first := primary_path head ready available valid
      exact prepend_keeps first (ih first.ready
        (fun value member => (available value member).grows _ _ first.growth first.history) first.valid)

/-- Supplied secondary node reads derive validity of their own returned tables. -/
theorem secondary_node
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.NodeTrace source path value before answer after}
    {memos saved : Memos} (reads : SourceCurrentSecondaryMemos.NodeReads trace memos saved)
    (ready : Ready before) (available : Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  revert ready available valid
  induction reads using SourceCurrentSecondaryMemos.NodeReads.rec
      (motive_2 := fun {values _index _path before _answer after} _ memos saved _ =>
        Ready before → (∀ value ∈ values, Available before value) → Valid before memos → Keeps before after saved)
      (motive_3 := fun {_index _path edges before _answer after} _ memos saved _ =>
        Ready before → (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) →
          Valid before memos → Keeps before after saved) with
  | empty | reference | union | finite | endpoint =>
      intro ready available valid
      exact pure_keeps _ _ ready valid
  | branches slow trace ih =>
      intro ready available valid
      exact ih ready (fun value member => available.children value member) valid
  | constrained blocked actual =>
      intro ready available valid
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available _ valid.query.predicate
      exact pure_keeps _ _ ready ⟨valid.unfolding, valid.query.descendants, by simpa only [actual] using checked.2⟩
  | closed plain closed actual =>
      intro ready available valid
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available _ valid.query.predicate
      exact pure_keeps _ _ ready ⟨valid.unfolding, valid.query.descendants, by simpa only [actual] using checked.2⟩
  | unfold plain opened actual predicate unfolding trace ih =>
      intro ready available valid
      have first := unfold_step actual predicate unfolding ready available valid
      exact prepend_keeps first.1 (ih first.1.ready first.2 first.1.valid)
  | missing absent ready available valid =>
      exact pure_keeps _ _ ready valid
  | present found trace ih ready available valid =>
      exact ih ready (available _ (List.mem_of_getElem? found)) valid
  | nil ready available valid =>
      exact pure_keeps _ _ ready valid
  | stop head ih ready available valid =>
      exact ih ready (fun value member => available value (by simp [member])) valid
  | next head tail headIH tailIH ready available valid =>
      have first := headIH ready (fun value member => available value (by simp [member])) valid
      exact prepend_keeps first (tailIH first.ready
        (fun value member => (available value (by simp [member])).grows _ _ first.growth first.history) first.valid)

/-- Supplied secondary child reads preserve their exact returned tables. -/
theorem secondary_child
    {values : List (Value Symbol Guard)} {index : Nat} {path : Path}
    {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.ChildTrace source values index path before answer after}
    {memos saved : Memos} (reads : SourceCurrentSecondaryMemos.ChildReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ values, Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  cases reads with
  | missing => exact pure_keeps _ _ ready valid
  | present found called => exact secondary_node called ready (available _ (List.mem_of_getElem? found)) valid

/-- Supplied secondary row reads thread each actual returned heap and memo bundle. -/
theorem secondary_edges
    {index : Nat} {path : Path} {edges : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.EdgesTrace source index path edges before answer after}
    {memos saved : Memos} (reads : SourceCurrentSecondaryMemos.EdgesReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available before value)
    (valid : Valid before memos) : Keeps before after saved := by
  revert ready available valid
  induction reads using SourceCurrentSecondaryMemos.EdgesReads.rec
      (motive_1 := fun {_path _value _before _answer _after} _ _ _ _ => True)
      (motive_2 := fun {_values _index _path _before _answer _after} _ _ _ _ => True) with
  | empty | reference | union | finite | endpoint | branches | constrained | closed | unfold | missing | present => trivial
  | nil => intro ready available valid; exact pure_keeps _ _ ready valid
  | stop head _ =>
      intro ready available valid
      exact secondary_child head ready (fun value member => available value (by simp [member])) valid
  | next head tail _ ih =>
      intro ready available valid
      have first := secondary_child head ready (fun value member => available value (by simp [member])) valid
      exact prepend_keeps first (ih first.ready
        (fun value member => (available value (by simp [member])).grows _ _ first.growth first.history) first.valid)

/-- Supplied secondary path reads derive validity without choosing a different schedule. -/
theorem secondary_path
    {values : List (Value Symbol Guard)} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.PathTrace source values path before answer after}
    {memos saved : Memos} (reads : SourceCurrentSecondaryMemos.PathReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ values, Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  cases reads with
  | empty => exact pure_keeps _ _ ready valid
  | child called => exact secondary_child called ready available valid

/-- Supplied secondary class reads retain validity across the exact visited path prefix. -/
theorem secondary_class
    {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.ClassTrace source values paths before answer after}
    {memos saved : Memos} (reads : SourceCurrentSecondaryMemos.ClassReads trace memos saved)
    (ready : Ready before) (available : ∀ value ∈ values, Available before value) (valid : Valid before memos) :
    Keeps before after saved := by
  revert ready available valid
  induction reads with
  | nil => intro ready available valid; exact pure_keeps _ _ ready valid
  | stop head => intro ready available valid; exact secondary_path head ready available valid
  | next head tail ih =>
      intro ready available valid
      have first := secondary_path head ready available valid
      exact prepend_keeps first (ih first.ready
        (fun value member => (available value member).grows _ _ first.growth first.history) first.valid)

end MicroCFTA.SourceCurrentAllocatedGateReadValidity
