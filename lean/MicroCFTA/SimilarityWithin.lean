import MicroCFTA.MinimizeSchedule

/-!
# Ordered similarity pairs within structural classes

The source builds ordered class queues, then removes the current transition
from its queue while it traverses the original transition order. This module
compares that stateful schedule with filtering the original unordered pairs.
-/
namespace MicroCFTA.SimilarityWithin
open MinimizeSchedule

/-- The finite-map lookup view. A missing key has an empty queue. -/
abbrev Queues (Key Item : Type) := Key → List Item

/-- Insert one class queue without changing another key. -/
def put [DecidableEq Key] (queues : Queues Key Item) (key : Key) (values : List Item) : Queues Key Item :=
  fun wanted => if wanted = key then values else queues wanted

/-- Map.fromListWith (flip (<>)) appends each occurrence after earlier occurrences. -/
def appendEntry [DecidableEq Key] (queues : Queues Key Item) (entry : Key × Item) : Queues Key Item :=
  put queues entry.1 (queues entry.1 ++ [entry.2])

/-- The source map construction processes entries from left to right. -/
def group [DecidableEq Key] (entries : List (Key × Item)) : Queues Key Item :=
  entries.foldl appendEntry (fun _ => [])

/-- Independent ordered members of one class. -/
def members [DecidableEq Key] (key : Key) (entries : List (Key × Item)) : List Item :=
  entries.filterMap (fun entry => if entry.1 = key then some entry.2 else none)

/-- Appending a source occurrence extends exactly its class queue. -/
theorem group_acc [DecidableEq Key] (entries : List (Key × Item))
    (queues : Queues Key Item) (key : Key) :
    entries.foldl appendEntry queues key = queues key ++ members key entries := by
  induction entries generalizing queues with
  | nil => simp [members]
  | cons entry rest ih =>
      rw [List.foldl_cons, ih]
      by_cases same : entry.1 = key
      · subst key
        simp [appendEntry, put, members, List.append_assoc]
      · have other : key ≠ entry.1 := Ne.symm same
        simp [appendEntry, put, members, same, other]

/-- The constructed map contains every class occurrence in its original order. -/
theorem group_members [DecidableEq Key] (entries : List (Key × Item)) (key : Key) :
    group entries key = members key entries := by
  simpa [group] using group_acc entries (fun _ => []) key

/-- One actual mapAccumL step. The source removes the head without comparing values. -/
def later [DecidableEq Key] (queues : Queues Key Item) (entry : Key × Item) :
    Queues Key Item × List (Item × Item) :=
  match queues entry.1 with
  | [] => (queues, [])
  | _ :: rest => (put queues entry.1 rest, rest.map (entry.2, ·))

/-- Flatten the emitted mapAccumL rows in source traversal order. -/
def walk [DecidableEq Key] (queues : Queues Key Item) : List (Key × Item) → List (Item × Item)
  | [] => []
  | entry :: rest =>
      let next := later queues entry
      next.2 ++ walk next.1 rest

/-- The independent reference pairs each occurrence with later occurrences of its class. -/
def reference [DecidableEq Key] : List (Key × Item) → List (Item × Item)
  | [] => []
  | entry :: rest => (members entry.1 rest).map (entry.2, ·) ++ reference rest

/-- Removing the current head leaves the exact queues for the remaining source traversal. -/
theorem later_invariant [DecidableEq Key] (entry : Key × Item) (rest : List (Key × Item))
    (queues : Queues Key Item) (exact : ∀ key, queues key = members key (entry :: rest)) :
    (later queues entry).2 = (members entry.1 rest).map (entry.2, ·) ∧
      ∀ key, (later queues entry).1 key = members key rest := by
  have current : queues entry.1 = entry.2 :: members entry.1 rest := by
    simpa [members] using exact entry.1
  refine ⟨by simp [later, current], ?_⟩
  intro key
  simp only [later, current]
  by_cases same : key = entry.1
  · simp [put, same]
  · have other : entry.1 ≠ key := Ne.symm same
    simpa [put, same, members, other] using exact key

/-- No queue miss is possible during a traversal initialized by its own grouped rows. -/
theorem walk_reference [DecidableEq Key] (entries : List (Key × Item))
    (queues : Queues Key Item) (exact : ∀ key, queues key = members key entries) :
    walk queues entries = reference entries := by
  induction entries generalizing queues with
  | nil => rfl
  | cons entry rest ih =>
      have step := later_invariant entry rest queues exact
      change (later queues entry).2 ++ walk (later queues entry).1 rest = _
      rw [step.1, ih _ step.2]
      rfl

/-- The actual grouped schedule. -/
def scheduled [DecidableEq Key] (entries : List (Key × Item)) : List (Item × Item) :=
  walk (group entries) entries

theorem scheduled_reference [DecidableEq Key] (entries : List (Key × Item)) :
    scheduled entries = reference entries :=
  walk_reference entries (group entries) (group_members entries)

/-- Exclude unclassified transitions while retaining the original transition order. -/
def classified (classify : Item → Option Key) (items : List Item) : List (Key × Item) :=
  items.filterMap (fun item => (classify item).map (fun key => (key, item)))

/-- The original unordered pair is eligible exactly when both classes exist and agree. -/
def eligible [DecidableEq Key] (classify : Item → Option Key) (pair : Item × Item) : Bool :=
  match classify pair.1, classify pair.2 with
  | some first, some second => decide (first = second)
  | _, _ => false

/-- The class queue is the matching subsequence of the original transition list. -/
theorem classified_members [DecidableEq Key] (classify : Item → Option Key) (items : List Item) (key : Key) :
    members key (classified classify items) = items.filter (fun item => decide (classify item = some key)) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases found : classify item with
      | none => simpa [classified, members, found] using ih
      | some actual =>
          by_cases same : actual = key
          · subst actual
            simpa [classified, members, found] using congrArg (item :: ·) ih
          · simpa [classified, members, found, same] using ih

/-- Filtering one row of unorderedPairs keeps precisely the later same-class transitions. -/
theorem pair_row [DecidableEq Key] (classify : Item → Option Key) (item : Item) (rest : List Item) :
    ((rest.map (item, ·)).filter (eligible classify)) =
      match classify item with
      | none => []
      | some key => (rest.filter (fun other => decide (classify other = some key))).map (item, ·) := by
  cases first : classify item with
  | none =>
      induction rest with
      | nil => rfl
      | cons other rest ih => simp [eligible, first]
  | some key =>
      induction rest with
      | nil => rfl
      | cons other rest ih =>
          cases second : classify other with
          | none => simpa [eligible, first, second] using ih
          | some actual =>
              by_cases same : actual = key
              · subst actual
                simpa [eligible, first, second] using congrArg ((item, other) :: ·) ih
              · have other : key ≠ actual := Ne.symm same
                simpa [eligible, first, second, same, other] using ih

/-- Ordered list equality proves both completeness and the exact first-error schedule. -/
theorem reference_filtered [DecidableEq Key] (classify : Item → Option Key) (items : List Item) :
    reference (classified classify items) = (unorderedPairs items).filter (eligible classify) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rw [unorderedPairs, List.filter_append, pair_row]
      cases found : classify item with
      | none => simpa [classified, found] using ih
      | some key =>
          simp only [classified, List.filterMap_cons, found, Option.map_some, reference]
          change (members key (classified classify rest)).map (item, ·) ++
            reference (classified classify rest) = _
          rw [classified_members, ih]

/-- similarityWithin emits exactly the eligible original pairs, in the original order. -/
theorem scheduled_filtered [DecidableEq Key] (classify : Item → Option Key) (items : List Item) :
    scheduled (classified classify items) = (unorderedPairs items).filter (eligible classify) := by
  rw [scheduled_reference, reference_filtered]

/-- Eligibility is symmetric, including unclassified transitions. -/
theorem eligible_symm [DecidableEq Key] (classify : Item → Option Key) (first second : Item) :
    eligible classify (first, second) = eligible classify (second, first) := by
  cases left : classify first <;> cases right : classify second <;> simp [eligible, left, right, eq_comm]

/-- Skipping a pair rejected in both directions leaves inference and its first error unchanged. -/
theorem inferPairs_filter (oracle : Address → Address → Guards.Verdict)
    (keep : Address × Address → Bool) (pairs : List (Address × Address))
    (outside : ∀ pair ∈ pairs, keep pair = false →
      oracle pair.1 pair.2 = .no ∧ oracle pair.2 pair.1 = .no) :
    inferPairs oracle (pairs.filter keep) = inferPairs oracle pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      have tail := ih (fun pair member => outside pair (by simp [member]))
      cases kept : keep pair with
      | true => simp only [List.filter_cons, kept, ↓reduceIte, inferPairs]; rw [tail]
      | false =>
          have rejected := outside pair (by simp) kept
          cases pair
          simp [kept, inferPairs, inferDirection, rejected.1, rejected.2, tail]
          cases inferPairs oracle rest <;> rfl

/-- The optimized similarity result equals ordinary similarity for a class-restricted oracle.
The equality includes unresolved-direction errors and deterministic direction preference. -/
theorem similarityWithin_exact [DecidableEq Key] (classify : Address → Option Key)
    (oracle : Address → Address → Guards.Verdict) (items : List Address)
    (outside : ∀ first second, eligible classify (first, second) = false → oracle first second = .no) :
    inferPairs oracle (scheduled (classified classify items)) = inferPairs oracle (unorderedPairs items) := by
  rw [scheduled_filtered]
  apply inferPairs_filter
  intro pair member excluded
  exact ⟨outside _ _ excluded, outside _ _ (by rw [← eligible_symm]; exact excluded)⟩

/-- The structural classification guard in refinementSubtypingOn rejects every other pair. -/
def restrictedOracle [DecidableEq Key] (classify : Address → Option Key)
    (entails : Address → Address → Guards.Verdict) (first second : Address) : Guards.Verdict :=
  if eligible classify (first, second) then entails first second else .no

/-- The source refinement oracle adapter supplies the off-class No condition itself. -/
theorem similarityWithin_restricted [DecidableEq Key] (classify : Address → Option Key)
    (entails : Address → Address → Guards.Verdict) (items : List Address) :
    inferPairs (restrictedOracle classify entails) (scheduled (classified classify items)) =
      inferPairs (restrictedOracle classify entails) (unorderedPairs items) := by
  apply similarityWithin_exact
  intro first second outside
  simp [restrictedOracle, outside]

/-- The emitted list contains every eligible original pair and no other pair. -/
theorem scheduled_members [DecidableEq Key] (classify : Item → Option Key) (items : List Item) (pair : Item × Item) :
    pair ∈ scheduled (classified classify items) ↔
      pair ∈ unorderedPairs items ∧ eligible classify pair = true := by
  rw [scheduled_filtered]
  exact List.mem_filter

/-- The optimization never emits more pairs than the original quadratic traversal. -/
theorem scheduled_length_le [DecidableEq Key] (classify : Item → Option Key) (items : List Item) :
    (scheduled (classified classify items)).length ≤ (unorderedPairs items).length := by
  rw [scheduled_filtered]
  exact List.length_filter_le _ _

/-- The number of unordered pairs in a class of the given size. -/
def pairCount : Nat → Nat
  | 0 => 0
  | size + 1 => size + pairCount size

theorem unorderedPairs_length (items : List Item) : (unorderedPairs items).length = pairCount items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [unorderedPairs, pairCount, ih]

/-- Each class pays only for its own pairs. -/
def budget [DecidableEq Key] (keys : List Key) (entries : List (Key × Item)) : Nat :=
  (keys.map (fun key => pairCount (members key entries).length)).sum

/-- Updating one distinct map key increases a summed counter only once. -/
theorem sum_increment [DecidableEq Key] (keys : List Key) (distinct : keys.Nodup)
    (key : Key) (present : key ∈ keys) (counts : Key → Nat) (extra : Nat) :
    (keys.map (fun found => if found = key then counts found + extra else counts found)).sum =
      (keys.map counts).sum + extra := by
  induction keys with
  | nil => simp at present
  | cons first rest ih =>
      have nodup := List.nodup_cons.mp distinct
      by_cases same : first = key
      · subst first
        have unchanged : rest.map (fun found => if found = key then counts found + extra else counts found) =
            rest.map counts := by
          apply List.map_congr_left
          intro found member
          have different : found ≠ key := by intro equal; subst found; exact nodup.1 member
          simp [different]
        simp only [List.map_cons, ↓reduceIte, List.sum_cons]
        rw [unchanged]
        omega
      · have inRest : key ∈ rest := by simpa [List.mem_cons, Ne.symm same] using present
        simpa [same, Nat.add_assoc] using congrArg (counts first + ·) (ih nodup.2 inRest)

/-- The exact number of emitted pairs is the sum of class-local pair counts. -/
theorem reference_budget [DecidableEq Key] (entries : List (Key × Item))
    (keys : List Key) (distinct : keys.Nodup) (complete : ∀ entry ∈ entries, entry.1 ∈ keys) :
    (reference entries).length = budget keys entries := by
  induction entries with
  | nil =>
      simp only [reference, List.length_nil, budget, members, List.filterMap_nil, pairCount]
      clear complete distinct
      induction keys with
      | nil => rfl
      | cons key rest ih => simpa only [List.map_cons, List.sum_cons, Nat.zero_add] using ih
  | cons entry rest ih =>
      have tail := ih (fun entry member => complete entry (by simp [member]))
      have increase := sum_increment keys distinct entry.1 (complete entry (by simp))
        (fun key => pairCount (members key rest).length) (members entry.1 rest).length
      have counts : keys.map (fun key => pairCount (members key (entry :: rest)).length) =
          keys.map (fun key => if key = entry.1 then
            pairCount (members key rest).length + (members entry.1 rest).length
            else pairCount (members key rest).length) := by
        apply List.map_congr_left
        intro key member
        by_cases same : key = entry.1
        · subst key
          simp only [members, List.filterMap_cons, ↓reduceIte, List.length_cons, pairCount]
          omega
        · have other := Ne.symm same
          simp [members, same, other]
      simp only [reference, List.length_append, List.length_map, tail, budget, counts]
      rw [increase]
      omega

private theorem keys_distinct [DecidableEq Key] (keys : List Key) : keys.eraseDups.Nodup := by
  cases keys with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp only [List.mem_eraseDups, List.mem_filter]
        intro member
        simpa using member.2
      · exact keys_distinct _
termination_by keys.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- The source grouped map supplies its own complete, duplicate-free class key list. -/
theorem scheduled_budget [DecidableEq Key] (entries : List (Key × Item)) :
    (scheduled entries).length = budget (entries.map Prod.fst).eraseDups entries := by
  rw [scheduled_reference]
  apply reference_budget
  · exact keys_distinct _
  · intro entry member
    simp only [List.mem_eraseDups]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩

/-- The exact output pair count is half of size times its predecessor. -/
theorem pairCount_twice (size : Nat) : 2 * pairCount size = size * (size - 1) := by
  induction size with
  | zero => rfl
  | succ size ih =>
      cases size with
      | zero => rfl
      | succ size =>
          simp only [pairCount, Nat.add_sub_cancel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at ih ⊢
          omega

theorem pairCount_closed (size : Nat) : pairCount size = size * (size - 1) / 2 := by
  rw [← pairCount_twice]
  omega

/-- Exact source pair work is the sum of n*(n-1)/2 over the class sizes. -/
theorem scheduled_class_cost [DecidableEq Key] (entries : List (Key × Item)) :
    (scheduled entries).length =
      ((entries.map Prod.fst).eraseDups.map (fun key =>
        (members key entries).length * ((members key entries).length - 1) / 2)).sum := by
  rw [scheduled_budget]
  simp [budget, pairCount_closed]

/-- Interleaved classes retain original pair order instead of map-key order. -/
example : scheduled [(1, 10), (0, 20), (1, 30), (0, 40), (1, 50)] =
    [(10, 30), (10, 50), (20, 40), (30, 50)] := by cbv

/-- Equal values retain separate input occurrences. -/
example : scheduled [(0, 7), (0, 7), (0, 7)] = [(7, 7), (7, 7), (7, 7)] := by cbv

/-- Unclassified transitions create no pair and do not alter the order of retained pairs. -/
example : scheduled (classified (fun value : Nat => if value = 9 then none else some (value % 2))
    [1, 9, 3, 2, 4]) = [(1, 3), (2, 4)] := by cbv

/-- Interleaved classes keep the original first unresolved query. -/
example : inferPairs (fun _ _ => .unknown)
    (scheduled (classified (fun address : Address => some (address.node % 2))
      [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩])) = .error (.unknown ⟨0, 0⟩ ⟨2, 0⟩) := by cbv

end MicroCFTA.SimilarityWithin
