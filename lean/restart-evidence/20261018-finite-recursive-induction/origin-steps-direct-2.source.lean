import MicroCFTA.SourceCurrentOpenObservations

/-!
# Finite step witnesses for actual open origins

Each witness counts actual epsilon steps at one fixed reader. Union and
Mu exposure remove one step from this witness. A Mu step retains its
actual stored execution. The tail keeps the original reader heap.
No reader transport, generated-value availability, or completion law is
assumed. The witness count does not bound all recursive execution.
-/
namespace MicroCFTA.SourceCurrentOpenOriginSteps
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open Productivity (Reachable)
open InternedBinderProtocol (Reference NodeKey)
open InternedEdgeResidency (nodeEdges)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (ReferenceOrigin)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A path counts front epsilon steps at one fixed observation heap. -/
def Path (reader : State Symbol Guard) : Nat → Value Symbol Guard → Value Symbol Guard → Prop
  | 0, first, last => first = last
  | steps + 1, first, last => ∃ next ∈ successors reader first, Path reader steps next last

/-- A row witness ends at one complete physical row after the stated epsilon steps. -/
def RowAt (reader : State Symbol Guard) (steps : Nat) (first : Value Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  ∃ last, Path reader steps first last ∧ row ∈ nodeEdges last

private theorem path_snoc (reader : State Symbol Guard) {steps : Nat}
    {first middle last : Value Symbol Guard} (path : Path reader steps first middle)
    (member : last ∈ successors reader middle) : Path reader (steps + 1) first last := by
  induction steps generalizing first with
  | zero =>
      cases path
      exact ⟨last,member,rfl⟩
  | succ steps ih =>
      obtain ⟨next,present,tail⟩ := path
      exact ⟨next,present,ih tail⟩

/-- Every counted path is an actual path in the repaired epsilon graph. -/
theorem Path.reachable (reader : State Symbol Guard) {steps : Nat}
    {first last : Value Symbol Guard} (path : Path reader steps first last) :
    Reachable (successors reader) [first] last := by
  induction steps generalizing first with
  | zero =>
      cases path
      exact .seed List.mem_cons_self
  | succ steps ih =>
      obtain ⟨next,present,tail⟩ := path
      exact EpsilonUnion.reach_trans _ first next last (.step (.seed List.mem_cons_self) present) (ih tail)

/-- Every actual reachable value has a finite step witness from an original seed. -/
theorem path_of_reachable (reader : State Symbol Guard) (roots : List (Value Symbol Guard))
    (last : Value Symbol Guard) (actual : Reachable (successors reader) roots last) :
    ∃ first ∈ roots, ∃ steps, Path reader steps first last := by
  induction actual with
  | seed present => exact ⟨_,present,0,rfl⟩
  | step _ member ih =>
      obtain ⟨first,present,steps,path⟩ := ih
      exact ⟨first,present,steps+1,path_snoc reader path member⟩

/-- Complete origins have exactly the finite row witnesses from their actual seeds. -/
theorem origin_iff (reader : State Symbol Guard) (roots : List (Value Symbol Guard))
    (row : EdgeValue Symbol Guard) :
    Origin reader roots row ↔ ∃ first ∈ roots, ∃ steps, RowAt reader steps first row := by
  constructor
  · rintro ⟨last,actual,member⟩
    obtain ⟨first,present,steps,path⟩ := path_of_reachable reader roots last actual
    exact ⟨first,present,steps,last,path,member⟩
  · rintro ⟨first,present,steps,last,path,member⟩
    exact ⟨last,EpsilonUnion.change_seeds _ [first] roots
      (fun value included => (List.mem_singleton.mp included) ▸ Reachable.seed present) _ path.reachable,member⟩

/-- Bare-reference observations have finite paths from their actual seed occurrences. -/
theorem reference_iff (reader : State Symbol Guard) (roots : List (Value Symbol Guard))
    (name : Reference) :
    ReferenceOrigin reader roots name ↔
      ∃ first ∈ roots, ∃ steps, Path reader steps first (.reference name) := by
  constructor
  · exact path_of_reachable reader roots (.reference name)
  · rintro ⟨first,present,steps,path⟩
    exact EpsilonUnion.change_seeds _ [first] roots
      (fun value included => (List.mem_singleton.mp included) ▸ Reachable.seed present) _ path.reachable

/-- Zero epsilon steps expose only the literal physical rows of the current value. -/
theorem row_zero (reader : State Symbol Guard) (first : Value Symbol Guard) (row : EdgeValue Symbol Guard) :
    RowAt reader 0 first row ↔ row ∈ nodeEdges first := by
  simp only [RowAt,Path]
  constructor
  · rintro ⟨last,rfl,member⟩
    exact member
  · exact fun member => ⟨first,rfl,member⟩

/-- One front epsilon step leaves a strictly shorter witness at the same reader. -/
theorem row_succ (reader : State Symbol Guard) (steps : Nat) (first : Value Symbol Guard)
    (row : EdgeValue Symbol Guard) :
    RowAt reader (steps + 1) first row ↔
      ∃ next ∈ successors reader first, RowAt reader steps next row := by
  constructor
  · rintro ⟨last,⟨next,present,path⟩,member⟩
    exact ⟨next,present,last,path,member⟩
  · rintro ⟨next,present,last,path,member⟩
    exact ⟨last,⟨next,present,path⟩,member⟩

/-- An ordinary value exposes a physical row without any epsilon step. -/
theorem row_node (reader : State Symbol Guard) (steps : Nat) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference) (row : EdgeValue Symbol Guard) :
    RowAt reader steps (.node entry rows depth free) row ↔ steps = 0 ∧ row ∈ rows := by
  cases steps with
  | zero => simp only [row_zero,nodeEdges,true_and]
  | succ steps => simp only [row_succ,successors,List.not_mem_nil,exists_false,Nat.succ_ne_zero,false_and]

/-- A union row witness selects an actual member and removes one epsilon step. -/
theorem row_union (reader : State Symbol Guard) (steps : Nat) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (row : EdgeValue Symbol Guard) :
    RowAt reader steps (.union entry members depth free) row ↔
      ∃ count, steps = count + 1 ∧ ∃ member ∈ members, RowAt reader count member row := by
  cases steps with
  | zero =>
      constructor
      · intro actual
        have impossible := (row_zero reader _ row).mp actual
        cases impossible
      · rintro ⟨count,impossible,_⟩
        cases impossible
  | succ steps =>
      constructor
      · intro actual
        exact ⟨steps,rfl,by simpa only [successors] using (row_succ reader steps _ row).mp actual⟩
      · rintro ⟨count,same,member,present,tail⟩
        have equal : steps = count := Nat.succ.inj same
        cases equal
        exact (row_succ reader steps _ row).mpr ⟨member,present,tail⟩

/-- A Mu row witness derives successful actual unfolding and a shorter original-reader tail. -/
theorem row_mu (reader : State Symbol Guard) (steps : Nat) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (row : EdgeValue Symbol Guard) :
    RowAt reader steps (.mu entry body depth ordinary) row ↔
      ∃ count result after, steps = count + 1 ∧
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) reader = .done result after ∧
        RowAt reader count result row := by
  cases steps with
  | zero =>
      constructor
      · intro actual
        have impossible := (row_zero reader _ row).mp actual
        cases impossible
      · rintro ⟨count,result,after,impossible,_⟩
        cases impossible
  | succ steps =>
      constructor
      · intro actual
        obtain ⟨next,present,tail⟩ := (row_succ reader steps _ row).mp actual
        cases called : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) reader with
        | pending key after => simp only [successors,called,List.not_mem_nil] at present
        | done result after =>
            have same : next = result := by simpa only [successors,called,List.mem_singleton] using present
            subst next
            exact ⟨steps,result,after,rfl,rfl,tail⟩
      · rintro ⟨count,result,after,same,called,tail⟩
        have equal : steps = count := Nat.succ.inj same
        cases equal
        exact (row_succ reader steps _ row).mpr ⟨result,by simp only [successors,called,List.mem_singleton],tail⟩

/-- A valid reader adds actual stored execution and growth receipts to the strict Mu step. -/
theorem row_mu_effects (reader : State Symbol Guard) (valid : Valid reader) (steps : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (actual : RowAt reader steps (.mu entry body depth ordinary) row) :
    ∃ count result after, steps = count + 1 ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) reader = .done result after ∧
      InternedFreshOrdinaryStoredSubstitution.execute body
        (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none)
        reader = .done result after ∧
      Valid after ∧ Grows reader after ∧ RowAt reader count result row := by
  obtain ⟨count,result,after,same,called,tail⟩ := (row_mu reader steps entry body depth ordinary row).mp actual
  have correct := InternedFreshOrdinaryStoredSubstitution.unfold_correct (.mu entry body depth ordinary) reader valid
  have facts : Valid after ∧ Grows reader after := by
    simpa only [called,InternedNestedConstruction.Outcome.state] using correct
  exact ⟨count,result,after,same,called,called,facts.1,facts.2,tail⟩

end MicroCFTA.SourceCurrentOpenOriginSteps
