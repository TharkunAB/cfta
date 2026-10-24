import MicroCFTA.Language
import MicroCFTA.UnionFind

/-!
# Enumeration fragments and value-slot assimilation

The constructors follow `Enumeration.TermFragment` and `UVarValue`. An
assignment supplies the complete term for each UVar. Graph contents have
their term-language interpretation. A suspended obligation can read both
the assignment and the term at its current position.

These proofs verify fragment renaming, stored-value intersection and slot
assimilation. They do not assume that the expansion scheduler or its caller
establishes the slot invariants. Concrete suspended-path construction and
recursive marker rendering remain separate obligations.
-/

namespace MicroCFTA.Fragments
open Language

/-- An ordered symbol fragment or a hole named by a union-find variable. -/
inductive Fragment (Symbol : Type) where
  | node (symbol : Symbol) (children : List (Fragment Symbol))
  | hole (uv : Nat)

/-- Replace every hole by its assigned complete term. -/
def fill (assignment : Nat → Term Symbol) : Fragment Symbol → Term Symbol
  | .node symbol children => .node symbol (children.map (fill assignment))
  | .hole uv => assignment uv

/-- Rename holes without changing symbol nodes or child order. -/
def rename (representative : Nat → Nat) : Fragment Symbol → Fragment Symbol
  | .node symbol children => .node symbol (children.map (rename representative))
  | .hole uv => .hole (representative uv)

/-- Renaming holes is equivalent to looking up the renamed assignment. -/
theorem fill_rename (assignment : Nat → Term Symbol) (representative : Nat → Nat)
    (fragment : Fragment Symbol) :
    fill assignment (rename representative fragment) = fill (assignment ∘ representative) fragment := by
  induction fragment using Fragment.rec
    (motive_2 := fun children =>
      (children.map (rename representative)).map (fill assignment) =
        children.map (fill (assignment ∘ representative))) with
  | node symbol children ih => simpa only [fill, rename] using congrArg (Term.node symbol) ih
  | hole uv => simp [fill, rename, Function.comp_def]
  | nil => rfl
  | cons child children ih ihs => simp only [List.map_cons, ih, ihs]

/-- Equal assignments produce equal completed fragments. -/
theorem fill_congr (left right : Nat → Term Symbol) (same : ∀ uv, left uv = right uv)
    (fragment : Fragment Symbol) : fill left fragment = fill right fragment := by
  have functions : left = right := funext same
  rw [functions]

/-- Resolving holes to their forest representatives preserves every permitted completion. -/
theorem fill_representatives (forest : UnionFind.Forest) (assignment : Nat → Term Symbol)
    (satisfies : UnionFind.Satisfies forest assignment) (representative : Nat → Nat)
    (paths : ∀ uv, ∃ size, UnionFind.Reaches forest uv (representative uv) size)
    (fragment : Fragment Symbol) : fill assignment (rename representative fragment) = fill assignment fragment := by
  rw [fill_rename]
  apply fill_congr
  intro uv
  obtain ⟨size, path⟩ := paths uv
  exact (satisfies uv (representative uv) (UnionFind.sameClass_root path)).symm

/-- Interpret one graph restriction as its accepted term language. -/
abbrev Domain (Symbol : Type) := Term Symbol → Prop

/-- An obligation at the current term can refer to the other assigned holes. -/
abbrev Obligation (Symbol : Type) := (Nat → Term Symbol) → Term Symbol → Prop

/-- A missing graph restriction permits any complete term. -/
def permits (domain : Option (Domain Symbol)) (term : Term Symbol) : Prop :=
  match domain with
  | none => True
  | some predicate => predicate term

/-- Intersect graph restrictions, retaining a sole restriction unchanged. -/
def intersectDomains : Option (Domain Symbol) → Option (Domain Symbol) → Option (Domain Symbol)
  | none, right => right
  | left, none => left
  | some left, some right => some (fun term => left term ∧ right term)

/-- Optional graph intersection means conjunction of accepted-term restrictions. -/
theorem intersectDomains_correct (left right : Option (Domain Symbol)) (term : Term Symbol) :
    permits (intersectDomains left right) term ↔ permits left term ∧ permits right term := by
  cases left <;> cases right <;> simp [intersectDomains, permits]

/-- Concrete synchronous graph intersection supplies the interpreted conjunction. -/
theorem graph_intersection_domain [DecidableEq Symbol]
    (left : Automaton Q Symbol) (right : Automaton R Symbol) (q : Q) (r : R) (term : Term Symbol) :
    Accepts (Language.intersect left right) (q, r) term ↔
      permits (intersectDomains (some (Accepts left q)) (some (Accepts right r))) term := by
  rw [accepts_intersect_iff]
  rfl

/-- The value states used by the enumeration engine. -/
inductive Slot (Symbol : Type) where
  | pending (domain : Option (Domain Symbol)) (obligations : List (Obligation Symbol))
  | expanded (fragment : Fragment Symbol)
  | eliminated

/-- Stored graph, suspended obligations, or fragment equations constrain one assigned term. -/
def slotSatisfies (assignment : Nat → Term Symbol) (uv : Nat) : Slot Symbol → Prop
  | .pending domain obligations =>
      permits domain (assignment uv) ∧ ∀ obligation ∈ obligations, obligation assignment (assignment uv)
  | .expanded fragment => fill assignment fragment = assignment uv
  | .eliminated => True

/-- Intersect only two unexpanded slots, as required by `intersectUVarValue`. -/
def intersectSlots : Slot Symbol → Slot Symbol → Option (Slot Symbol)
  | .pending left leftObligations, .pending right rightObligations =>
      some (.pending (intersectDomains left right) (leftObligations ++ rightObligations))
  | _, _ => none

/-- Successful slot intersection retains exactly both original restrictions. -/
theorem intersectSlots_correct (assignment : Nat → Term Symbol) (uv : Nat)
    (left right merged : Slot Symbol) (success : intersectSlots left right = some merged) :
    slotSatisfies assignment uv merged ↔
      slotSatisfies assignment uv left ∧ slotSatisfies assignment uv right := by
  cases left <;> cases right <;> simp only [intersectSlots] at success
  all_goals try cases success
  simp only [slotSatisfies, intersectDomains_correct, List.mem_append]
  grind only

/-- Equal assigned values satisfy the same unexpanded slot restrictions. -/
theorem openSlot_congr (assignment : Nat → Term Symbol) (left right : Nat)
    (same : assignment left = assignment right) (domain : Option (Domain Symbol))
    (obligations : List (Obligation Symbol)) :
    slotSatisfies assignment left (.pending domain obligations) ↔
      slotSatisfies assignment right (.pending domain obligations) := by
  simp only [slotSatisfies, same]

/-- A value-slot store indexed by union-find variables. -/
abbrev Heap (Symbol : Type) := Nat → Slot Symbol

/-- Replace one slot in a persistent store. -/
def setSlot (heap : Heap Symbol) (uv : Nat) (slot : Slot Symbol) : Heap Symbol :=
  fun other => if other = uv then slot else heap other

/-- All stored payload restrictions hold for the assignment. -/
def heapSatisfies (heap : Heap Symbol) (assignment : Nat → Term Symbol) : Prop :=
  ∀ uv, slotSatisfies assignment uv (heap uv)

/-- Move the source restrictions to the target, then eliminate the source slot. -/
def assimilate (heap : Heap Symbol) (target source : Nat) : Option (Heap Symbol) :=
  if target = source then some heap
  else match heap source with
    | .eliminated => some heap
    | sourceSlot => do
      let merged ← intersectSlots sourceSlot (heap target)
      some (setSlot (setSlot heap target merged) source .eliminated)

/-- Eliminating a merged slot is exact when union-find already equates its two variables. -/
theorem assimilate_correct (heap output : Heap Symbol) (target source : Nat)
    (assignment : Nat → Term Symbol) (equal : assignment target = assignment source)
    (success : assimilate heap target source = some output) :
    heapSatisfies output assignment ↔ heapSatisfies heap assignment := by
  by_cases same : target = source
  · simp [assimilate, same] at success
    subst output
    rfl
  · cases sourceSlot : heap source with
    | eliminated =>
      simp [assimilate, same, sourceSlot] at success
      subst output
      rfl
    | expanded fragment =>
      cases heap target <;> simp [assimilate, same, sourceSlot, intersectSlots] at success
    | pending sourceDomain sourceObligations =>
      cases targetSlot : heap target with
      | eliminated => simp [assimilate, same, sourceSlot, targetSlot, intersectSlots] at success
      | expanded fragment => simp [assimilate, same, sourceSlot, targetSlot, intersectSlots] at success
      | pending targetDomain targetObligations =>
        simp [assimilate, same, sourceSlot, targetSlot, intersectSlots] at success
        subst output
        constructor
        · intro after uv
          have targetRestrictions := after target
          simp only [setSlot, same, ↓reduceIte, slotSatisfies, intersectDomains_correct] at targetRestrictions
          by_cases atTarget : uv = target
          · subst uv
            rw [targetSlot]
            exact ⟨targetRestrictions.1.2,
              fun obligation member => targetRestrictions.2 obligation (List.mem_append_right _ member)⟩
          · by_cases atSource : uv = source
            · subst uv
              rw [sourceSlot]
              simp only [slotSatisfies, ← equal]
              exact ⟨targetRestrictions.1.1,
                fun obligation member => targetRestrictions.2 obligation (List.mem_append_left _ member)⟩
            · simpa [setSlot, atTarget, atSource] using after uv
        · intro before uv
          by_cases atSource : uv = source
          · subst uv
            simp [setSlot, slotSatisfies]
          · by_cases atTarget : uv = target
            · subst uv
              have hs := before source
              have ht := before target
              rw [sourceSlot] at hs
              rw [targetSlot] at ht
              simp only [slotSatisfies, ← equal] at hs ht
              simp only [setSlot, same, ↓reduceIte, slotSatisfies, intersectDomains_correct]
              refine ⟨⟨hs.1, ht.1⟩, ?_⟩
              intro obligation member
              rcases List.mem_append.mp member with left | right
              · exact hs.2 obligation left
              · exact ht.2 obligation right
            · simpa [setSlot, atSource, atTarget] using before uv

/-- A complete assignment satisfies both forest equalities and stored payloads. -/
def stateSatisfies (forest : UnionFind.Forest) (heap : Heap Symbol) (assignment : Nat → Term Symbol) : Prop :=
  UnionFind.Satisfies forest assignment ∧ heapSatisfies heap assignment

/-- Union followed by successful slot assimilation adds exactly one term equality. -/
theorem union_assimilate_correct (forest : UnionFind.Forest) (heap output : Heap Symbol)
    (valid : UnionFind.Total forest)
    (merged : UnionFind.union leftFuel rightFuel forest left right = some afterUnion)
    (assimilated : assimilate heap left right = some output) (assignment : Nat → Term Symbol) :
    stateSatisfies afterUnion output assignment ↔
      stateSatisfies forest heap assignment ∧ assignment left = assignment right := by
  constructor
  · rintro ⟨forestAfter, heapAfter⟩
    obtain ⟨forestBefore, equality⟩ := (UnionFind.union_satisfies valid merged assignment).mp forestAfter
    exact ⟨⟨forestBefore, (assimilate_correct heap output left right assignment equality assimilated).mp heapAfter⟩,
      equality⟩
  · rintro ⟨⟨forestBefore, heapBefore⟩, equality⟩
    exact ⟨(UnionFind.union_satisfies valid merged assignment).mpr ⟨forestBefore, equality⟩,
      (assimilate_correct heap output left right assignment equality assimilated).mpr heapBefore⟩

/-- Intersect a newly reached node and its inherited obligations into one value slot. -/
def mergeInto (heap : Heap Symbol) (uv : Nat) (domain : Option (Domain Symbol))
    (obligations : List (Obligation Symbol)) : Option (Heap Symbol) := do
  let merged ← intersectSlots (.pending domain obligations) (heap uv)
  some (setSlot heap uv merged)

/-- Node assimilation adds exactly its language and inherited obligation restrictions. -/
theorem mergeInto_correct (heap output : Heap Symbol) (uv : Nat)
    (domain : Option (Domain Symbol)) (obligations : List (Obligation Symbol))
    (assignment : Nat → Term Symbol) (success : mergeInto heap uv domain obligations = some output) :
    heapSatisfies output assignment ↔
      heapSatisfies heap assignment ∧ slotSatisfies assignment uv (.pending domain obligations) := by
  cases stored : heap uv with
  | eliminated => simp [mergeInto, stored, intersectSlots] at success
  | expanded fragment => simp [mergeInto, stored, intersectSlots] at success
  | pending previous previousObligations =>
    simp [mergeInto, stored, intersectSlots] at success
    subst output
    have localMeaning : slotSatisfies assignment uv
        (.pending (intersectDomains domain previous) (obligations ++ previousObligations)) ↔
        slotSatisfies assignment uv (.pending domain obligations) ∧ slotSatisfies assignment uv (heap uv) :=
      intersectSlots_correct assignment uv _ _ _ (by simp [stored, intersectSlots])
    constructor
    · intro after
      have atSlot := after uv
      simp only [setSlot, ↓reduceIte] at atSlot
      obtain ⟨added, original⟩ := localMeaning.mp atSlot
      refine ⟨?_, added⟩
      intro other
      by_cases same : other = uv
      · subst other; exact original
      · simpa [setSlot, same] using after other
    · rintro ⟨before, added⟩ other
      by_cases same : other = uv
      · subst other
        simp only [setSlot, ↓reduceIte]
        exact localMeaning.mpr ⟨added, before uv⟩
      · simpa [setSlot, same] using before other

/-- A slot whose graph language is empty admits no complete assignment. -/
theorem empty_slot_rejects (heap : Heap Symbol) (uv : Nat)
    (obligations : List (Obligation Symbol))
    (empty : heap uv = .pending (some (fun _ => False)) obligations) (assignment : Nat → Term Symbol) :
    ¬heapSatisfies heap assignment := by
  intro accepted
  have impossible := accepted uv
  rw [empty] at impossible
  exact impossible.1

/-- An automaton with no outgoing transition has an empty accepted language. -/
theorem empty_graph_rejects (automaton : Automaton State Symbol) (state : State)
    (empty : automaton state = []) (term : Term Symbol) : ¬Accepts automaton state term := by
  intro accepted
  cases accepted with
  | node edge children member runs guard => simp [empty] at member

end MicroCFTA.Fragments
