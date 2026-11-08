import MicroCFTA.SourceCurrentConjunctionCompletionReads
import MicroCFTA.MergedFreshOrdinaryColdReplay

set_option autoImplicit false

/-!
Successful demanded reads can repeat operands in any order. The first
read of each operand supplies its effects. Every later successful read
replays its rows without allocation. Compression retains the final heap
and covers every original row list. Read allowances can differ.
This result does not remove a failing last read or bound scan work.
-/
namespace MicroCFTA.SourceCurrentConjunctionFirstDemands
open InternedConstructorTemplates
open MergedFreshOrdinaryExposure (nodeEdges collect)
open MergedSourceExposure (Result)
open SourceEqualityProjectionRead (Read)
open SourceCurrentConjunctionCompletionReads (Exposures)

/-- Keep the first demand of each operand in its actual demand order. -/
def firstDemands {Key : Type} [DecidableEq Key] : List Key → List Key → List Key
  | _, [] => []
  | seen, node :: rest =>
      if node ∈ seen then firstDemands seen rest
      else node :: firstDemands (node :: seen) rest

/-- The scan keeps exactly the demanded operands not already seen. -/
theorem mem_firstDemands {Key : Type} [DecidableEq Key]
    (seen demands : List Key) (node : Key) :
    node ∈ firstDemands seen demands ↔ node ∈ demands ∧ node ∉ seen := by
  induction demands generalizing seen with
  | nil => simp only [firstDemands, List.not_mem_nil, false_and]
  | cons head rest ih =>
      by_cases present : head ∈ seen
      · simp only [firstDemands, ite_eq_left present, ih, List.mem_cons]
        by_cases same : node = head
        · subst node; simp only [present, not_true_eq_false, and_false]
        · simp only [same, false_or]
      · simp only [firstDemands, ite_eq_right present, List.mem_cons, ih]
        by_cases same : node = head
        · subst node; simp only [true_or, present, not_false_eq_true, and_true]
        · simp only [same, false_or]

/-- The first-demand scan has no repeated operand. -/
theorem firstDemands_nodup {Key : Type} [DecidableEq Key] (seen demands : List Key) :
    (firstDemands seen demands).Nodup := by
  induction demands generalizing seen with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
      by_cases present : head ∈ seen
      · simpa only [firstDemands, ite_eq_left present] using ih seen
      · simp only [firstDemands, ite_eq_right present]
        refine List.nodup_cons.mpr ⟨?_, ih (head :: seen)⟩
        intro member
        exact ((mem_firstDemands (head :: seen) rest head).mp member).2 List.mem_cons_self

/-- A finite original support bounds the number of first demands. -/
theorem firstDemands_length {Key : Type} [DecidableEq Key] (demands support : List Key)
    (included : ∀ node ∈ demands, node ∈ support) :
    (firstDemands [] demands).length ≤ support.length :=
  (firstDemands_nodup [] demands).length_le_of_subset
    (fun node member => included node ((mem_firstDemands [] demands node).mp member).1)

variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

private theorem nodeEdges_correct (fuel : Nat) (value : Node) (before : State Symbol Guard)
    (valid : Valid before) :
    Valid (nodeEdges fuel value before).state ∧ Grows before (nodeEdges fuel value before).state := by
  have fallback (current : State Symbol Guard) (currentValid : Valid current) (root : Node) :
      Valid ((collect fuel current [] [root]).canonical).state ∧
        Grows current ((collect fuel current [] [root]).canonical).state := by
    rw [MergedPreparedReaderEffects.canonical_state]
    exact MergedFreshOrdinaryColdReplay.collect_correct fuel current currentValid [] [root]
  cases value with
  | empty | reference | node => exact ⟨valid, grows_refl _⟩
  | union => exact fallback before valid _
  | mu entry body depth ordinary =>
      have first := InternedFreshOrdinaryStoredSubstitution.unfold_correct
        (.mu entry body depth ordinary) before valid
      cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) before with
      | pending key middle =>
          simpa only [nodeEdges, unfolded, InternedNestedConstruction.Outcome.state, Result.state] using first
      | done result middle =>
          have head : Valid middle ∧ Grows before middle := by
            simpa only [unfolded, InternedNestedConstruction.Outcome.state] using first
          cases result with
          | node => simpa only [nodeEdges, unfolded, Result.state] using head
          | empty | reference | union | mu =>
              have later := fallback middle head.1 (.mu entry body depth ordinary)
              simpa only [nodeEdges, unfolded] using
                (show Valid ((collect fuel middle [] [.mu entry body depth ordinary]).canonical).state ∧
                    Grows before ((collect fuel middle [] [.mu entry body depth ordinary]).canonical).state from
                  ⟨later.1, grows_trans head.2 later.2⟩)

private theorem read_correct {node : Node} {before after : State Symbol Guard} {rows : List Edge}
    (actual : Read node before rows after) (valid : Valid before) : Valid after ∧ Grows before after := by
  cases actual with
  | done fuel completed =>
      simpa only [completed, Result.state] using nodeEdges_correct fuel node before valid

/-- Every successful read prefix retains valid caches and all completed records. -/
theorem valid_grows {demands : List Node} {before after : State Symbol Guard}
    {rows : List (List Edge)} (actual : Exposures demands before rows after) (valid : Valid before) :
    Valid after ∧ Grows before after := by
  induction actual with
  | nil => exact ⟨valid, grows_refl _⟩
  | cons first rest ih =>
      have head := read_correct first valid
      have tail := ih head.1
      exact ⟨tail.1, grows_trans head.2 tail.2⟩

private theorem read_replay {node : Node} {before final after : State Symbol Guard} {rows : List Edge}
    (actual : Read node before rows final) (valid : Valid before) (growth : Grows final after) :
    Read node after rows after := by
  cases actual with
  | done fuel completed =>
      exact .done fuel (MergedFreshOrdinaryColdReplay.nodeEdges_replay fuel node before after valid rows final completed growth)

private def Cached (seen : List Node) (rows : List (List Edge)) (current : State Symbol Guard) : Prop :=
  ∀ node ∈ seen, ∃ own ∈ rows, Read node current own current

private theorem cached_grows {seen : List Node} {rows : List (List Edge)}
    {before after : State Symbol Guard} (cached : Cached seen rows before)
    (valid : Valid before) (growth : Grows before after) : Cached seen rows after := by
  intro node member
  obtain ⟨own, present, actual⟩ := cached node member
  exact ⟨own, present, read_replay actual valid growth⟩

variable [DecidableEq (Value Symbol Guard)]

private theorem compress_from {demands : List Node} {before after : State Symbol Guard}
    {rows : List (List Edge)} (actual : Exposures demands before rows after)
    (seen : List Node) (oldRows : List (List Edge)) (valid : Valid before)
    (cached : Cached seen oldRows before) :
    ∃ compactRows, Exposures (firstDemands seen demands) before compactRows after ∧
      ∀ row ∈ rows, row ∈ oldRows ∨ row ∈ compactRows := by
  induction actual generalizing seen oldRows with
  | nil => exact ⟨[], .nil, by intro row member; cases member⟩
  | @cons node before own middle demands more after first rest ih =>
      by_cases present : node ∈ seen
      · obtain ⟨stored, storedMember, replayed⟩ := cached node present
        have same := first.unique replayed
        have middleValid : Valid middle := by simpa only [same.2] using valid
        have middleCached : Cached seen oldRows middle := by simpa only [same.2] using cached
        obtain ⟨compact, compressed, covered⟩ := ih seen oldRows middleValid middleCached
        refine ⟨compact, ?_, ?_⟩
        · simpa only [firstDemands, ite_eq_left present, same.2] using compressed
        · intro row member
          rcases List.mem_cons.mp member with equal | later
          · subst row
            exact Or.inl (by simpa only [same.1] using storedMember)
          · exact covered row later
      · have head := read_correct first valid
        have previous := cached_grows cached valid head.2
        have next : Cached (node :: seen) (own :: oldRows) middle := by
          intro value member
          rcases List.mem_cons.mp member with equal | earlier
          · subst value
            exact ⟨own, List.mem_cons_self, read_replay first valid (grows_refl middle)⟩
          · obtain ⟨stored, storedMember, replayed⟩ := previous value earlier
            exact ⟨stored, List.mem_cons_of_mem _ storedMember, replayed⟩
        obtain ⟨compact, compressed, covered⟩ := ih (node :: seen) (own :: oldRows) head.1 next
        refine ⟨own :: compact, ?_, ?_⟩
        · simpa only [firstDemands, ite_eq_right present] using Exposures.cons first compressed
        · intro row member
          rcases List.mem_cons.mp member with equal | later
          · subst row; exact Or.inr List.mem_cons_self
          · rcases covered row later with earlier | retained
            · rcases List.mem_cons.mp earlier with equal | old
              · subst row; exact Or.inr List.mem_cons_self
              · exact Or.inl old
            · exact Or.inr (List.mem_cons_of_mem _ retained)

/-- Actual successful reads compress to their distinct first demands at the same final heap. -/
theorem compress {demands : List Node} {before after : State Symbol Guard} {rows : List (List Edge)}
    (actual : Exposures demands before rows after) (valid : Valid before) :
    ∃ compactRows, Exposures (firstDemands [] demands) before compactRows after ∧
      ∀ row ∈ rows, row ∈ compactRows := by
  obtain ⟨compact, compressed, covered⟩ := compress_from actual [] [] valid
    (by intro node member; cases member)
  exact ⟨compact, compressed, fun row member => (covered row member).resolve_left (by simp)⟩

/-- Original operand positions bound first demands without fixing demand order or tuple width. -/
theorem compress_supported {demands : List Node} {before after : State Symbol Guard} {rows : List (List Edge)}
    (actual : Exposures demands before rows after) (valid : Valid before) (support : List Node)
    (included : ∀ node ∈ demands, node ∈ support) :
    ∃ nodes compactRows, Exposures nodes before compactRows after ∧ nodes.Nodup ∧
      (∀ node, node ∈ nodes ↔ node ∈ demands) ∧ nodes.length ≤ support.length ∧
      ∀ row ∈ rows, row ∈ compactRows := by
  obtain ⟨compact, compressed, covered⟩ := compress actual valid
  exact ⟨firstDemands [] demands, compact, compressed, firstDemands_nodup [] demands,
    (by intro node; simpa only [List.not_mem_nil, not_false_eq_true, and_true] using mem_firstDemands [] demands node),
    firstDemands_length demands support included, covered⟩

end MicroCFTA.SourceCurrentConjunctionFirstDemands
