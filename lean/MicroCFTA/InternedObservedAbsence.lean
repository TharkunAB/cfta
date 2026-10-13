import MicroCFTA.InternedBoundaryAtoms
import MicroCFTA.InternedOccurrenceObservations
import MicroCFTA.InternedNestedProvenance

/-!
# Exact ordinary-constructor agreement from observed boundary absence

The relation preserves emptiness for every result. It requires exact
record equality when the first result has no forbidden boundary atom.
The forbidden set can include both fresh references and newly reserved
Mu identities. Ordinary and union construction preserve this relation.
-/
namespace MicroCFTA.InternedObservedAbsence
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys InternedEdgeResidency
open InternedBoundaryAtoms InternedOccurrenceObservations InternedEmptyNormalization
open InternedLiveEdges InternedNonemptyRecords
open InternedBinderProtocol (NodeRef Reference)

/-- The result contains none of the boundary identities whose appearance would expose a changed source input. -/
def Clear (forbidden : NodeRef → Prop) (value : Value Symbol Guard) : Prop :=
  ∀ item ∈ atoms value, ¬ forbidden item

/-- Related executions agree on emptiness and have exactly equal records whenever no forbidden boundary remains. -/
def Related (forbidden : NodeRef → Prop) (first second : Value Symbol Guard) : Prop :=
  (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧ (Clear forbidden first → first = second)

/-- An unchanged source input satisfies the relation for every forbidden set. -/
theorem related_refl (forbidden : NodeRef → Prop) (value : Value Symbol Guard) : Related forbidden value value :=
  ⟨Iff.rfl, fun _ => rfl⟩

/-- Replacing a forbidden fresh reference by another reference preserves the observation. -/
theorem related_reference (forbidden : NodeRef → Prop) (first second : Reference) (fresh : forbidden (.ref first)) :
    Related forbidden (Value.reference (Symbol := Symbol) (Guard := Guard) first) (.reference second) := by
  refine ⟨by simp [Value.referenceOf], ?_⟩
  intro clear
  exact False.elim (clear (.ref first) (by simp [atoms]) fresh)

/-- Related ordered inputs agree on whether they contain an empty child. -/
theorem any_empty (forbidden : NodeRef → Prop) (first second : List (Value Symbol Guard))
    (paired : Paired (Related forbidden) first second) :
    first.any (fun child => child.referenceOf == .empty) = true ↔ second.any (fun child => child.referenceOf == .empty) = true := by
  simpa only [List.any_eq_true, beq_iff_eq] using
    exists_iff paired (fun value => value.referenceOf = .empty) (fun value => value.referenceOf = .empty) (fun _ _ related => related.1)

/-- Related ordered inputs have the same live-edge decision. -/
theorem all_live (forbidden : NodeRef → Prop) (first second : List (Value Symbol Guard))
    (paired : Paired (Related forbidden) first second) :
    first.any (fun child => child.referenceOf == .empty) = false ↔ second.any (fun child => child.referenceOf == .empty) = false := by
  simpa only [List.any_eq_false, beq_iff_eq] using
    all_iff paired (fun value => value.referenceOf ≠ .empty) (fun value => value.referenceOf ≠ .empty) (fun _ _ related => not_congr related.1)

/-- Boundary absence in all first operands turns the paired relation into exact list equality. -/
theorem paired_equal (forbidden : NodeRef → Prop) (first second : List (Value Symbol Guard))
    (paired : Paired (Related forbidden) first second) (clear : ∀ value ∈ first, Clear forbidden value) : first = second := by
  induction paired with
  | nil => rfl
  | @cons first second rest tail related paired ih =>
      rw [related.2 (clear first List.mem_cons_self), ih (fun value member => clear value (List.mem_cons_of_mem _ member))]

/-- The same finite constructor request has the same result in two histories with a common extension. -/
theorem run_shared [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (left right common : State Symbol Guard) (lv : InternedConstructorTemplates.Valid left) (rv : InternedConstructorTemplates.Valid right)
    (lg : Grows (run computation left).2 common) (rg : Grows (run computation right).2 common) :
    (run computation left).1 = (run computation right).1 := by
  have a := replay computation left common lv lg
  have b := replay computation right common rv rg
  have same := congrArg (fun pair : Result × State Symbol Guard => pair.1) (a.symm.trans b)
  exact same

/-- A source edge pair retains its symbol, guard, and related ordered child payloads. -/
def EdgeRelated (forbidden : NodeRef → Prop) (first second : EdgeValue Symbol Guard) : Prop :=
  first.entry.key.symbol = second.entry.key.symbol ∧ first.entry.key.constraint = second.entry.key.constraint ∧
    Paired (Related forbidden) first.children second.children

/-- Exact related child payloads determine the same resident edge in the common cache. -/
theorem edge_equal (forbidden : NodeRef → Prop) (first second : EdgeValue Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (left : EdgeResident state first) (right : EdgeResident state second)
    (related : EdgeRelated forbidden first second) (clear : ∀ value ∈ first.children, Clear forbidden value) : first = second := by
  have childrenSame := paired_equal forbidden first.children second.children related.2.2 clear
  have leftFields := (coherent.edges first.entry.key first left).2.2
  have rightFields := (coherent.edges second.entry.key second right).2.2
  have keyChildren : first.entry.key.children = second.entry.key.children := by
    rw [← leftFields, ← rightFields, childrenSame]
  have keys : first.entry.key = second.entry.key := by
    have symbol := related.1
    have guard := related.2.1
    cases leftKey : first.entry.key
    cases rightKey : second.entry.key
    simp only [leftKey, rightKey] at symbol guard keyChildren
    simp_all
  unfold EdgeResident at left right
  rw [← keys] at right
  exact Option.some.inj (left.symm.trans right)

/-- Related dead edges disappear together; related live edges agree exactly when their boundaries are clear. -/
theorem surviving_equal (forbidden : NodeRef → Prop) (first second : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state)
    (left : ∀ edge ∈ first, EdgeResident state edge) (right : ∀ edge ∈ second, EdgeResident state edge)
    (paired : Paired (EdgeRelated forbidden) first second)
    (clear : ∀ edge ∈ first, edge.children.any (fun child => child.referenceOf == .empty) = false →
      ∀ child ∈ edge.children, Clear forbidden child) : surviving first = surviving second := by
  induction paired with
  | nil => rfl
  | @cons first second rest tail related paired ih =>
      have tailSame := ih (fun edge member => left edge (List.mem_cons_of_mem _ member))
        (fun edge member => right edge (List.mem_cons_of_mem _ member))
        (fun edge member => clear edge (List.mem_cons_of_mem _ member))
      have alive := all_live forbidden first.children second.children related.2.2
      cases firstLive : first.children.any (fun child => child.referenceOf == .empty) with
      | false =>
          have secondLive := alive.mp firstLive
          have same := edge_equal forbidden first second state coherent (left first List.mem_cons_self)
            (right second List.mem_cons_self) related (clear first List.mem_cons_self firstLive)
          simpa only [surviving, List.filter_cons, firstLive, secondLive, Bool.not_false, ↓reduceIte, same] using congrArg (second :: ·) tailSame
      | true =>
          have secondDead := (any_empty forbidden first.children second.children related.2.2).mp firstLive
          simpa [surviving, firstLive, secondDead] using tailSame

/-- Actual source nodes preserve exact agreement after every changed edge without a forbidden boundary has been removed. -/
theorem makeNode_related [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (first second : List (EdgeValue Symbol Guard)) (left right common : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (cf : Facts common)
    (lr : ∀ edge ∈ first, EdgeResident left edge) (rr : ∀ edge ∈ second, EdgeResident right edge)
    (paired : Paired (EdgeRelated forbidden) first second)
    (lg : Grows (run (makeNode first) left).2 common) (rg : Grows (run (makeNode second) right).2 common) :
    Related forbidden (run (makeNode first) left).1 (run (makeNode second) right).1 := by
  constructor
  · rw [makeNode_empty_iff first left lf.coherent lf.linked lr, makeNode_empty_iff second right rf.coherent rf.linked rr]
    exact all_iff paired _ _ (fun a b related => any_empty forbidden a.children b.children related.2.2)
  · intro observed
    have leftGrowth := grows_trans (InternedConstructorTemplates.run_correct (makeNode first) left lf.coherent.valid).2 lg
    have rightGrowth := grows_trans (InternedConstructorTemplates.run_correct (makeNode second) right rf.coherent.valid).2 rg
    have normalized := surviving_equal forbidden first second common cf.coherent
      (fun edge member => edge_grows left common leftGrowth edge (lr edge member))
      (fun edge member => edge_grows right common rightGrowth edge (rr edge member)) paired (by
        intro edge member live child present item included
        exact observed item (makeNode_atom first left lf.coherent lf.linked lr edge member live child present item included))
    have same : makeNode first = makeNode second := by unfold makeNode; rw [normalized]
    rw [← same] at rg ⊢
    exact run_shared _ left right common lf.coherent.valid rf.coherent.valid lg rg

/-- Actual source unions preserve exact agreement when no forbidden boundary remains in any original operand. -/
theorem makeUnion_related [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (first second : List (Value Symbol Guard)) (left right common : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second) (paired : Paired (Related forbidden) first second)
    (lg : Grows (run (makeUnion first) left).2 common) (rg : Grows (run (makeUnion second) right).2 common) :
    Related forbidden (run (makeUnion first) left).1 (run (makeUnion second) right).1 := by
  constructor
  · rw [makeUnion_empty_iff first left lf.coherent lf.linked ll ln li,
      makeUnion_empty_iff second right rf.coherent rf.linked rl rn ri]
    exact all_iff paired _ _ (fun _ _ related => related.1)
  · intro observed
    have same := paired_equal forbidden first second paired (by
      intro value member item included
      exact observed item ((makeUnion_atom_iff first left lf.coherent lf.cached lf.linked ll li item).mpr ⟨value, member, included⟩))
    rw [← same] at rg ⊢
    exact run_shared _ left right common lf.coherent.valid rf.coherent.valid lg rg

end MicroCFTA.InternedObservedAbsence
