import MicroCFTA.SourceRecursiveIntersectionDescriptorCarrier

namespace MicroCFTA.SourceRecursiveIntersectionDomain

/-- Selects a typed canonical witness with the requested support in both pools. -/
private theorem choice_fields_witness
    (namePool : List Nat) (pairPool : List (Nat × Nat))
    (wanted : MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey) :
    let empty : MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey := ⟨[], []⟩
    let anchor := MicroCFTA.IntersectSchedule.pair
      MicroCFTA.IntersectSchedule.Input.empty MicroCFTA.IntersectSchedule.Input.empty
    let pairChoices := List.foldr
      (fun pair keys => keys ++ keys.map (fun key => extend key [] pair))
      [empty] pairPool
    let choices := List.foldr
      (fun name keys => keys ++ keys.map (fun key =>
        MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey.mk
          (extend key [name] anchor).free key.seen))
      pairChoices namePool
    ∃ key, key ∈ choices ∧
      MicroCFTA.IntersectionFlatMemoKeyDomain.Canonical key ∧ Typed key ∧
      (∀ name, name ∈ names key ↔ name ∈ names wanted ∧ name ∈ namePool) ∧
      (∀ pair, pair ∈ key.seen ↔ pair ∈ wanted.seen ∧ pair ∈ pairPool) := by
  dsimp only
  induction namePool with
  | nil =>
    rw [List.foldr_nil]
    induction pairPool with
    | nil =>
      rw [List.foldr_nil]
      refine ⟨⟨[], []⟩, ?_, ?_, ?_, ?_, ?_⟩
      · exact List.mem_cons.mpr (.inl rfl)
      · exact ⟨List.Pairwise.nil, List.Pairwise.nil⟩
      · intro entry member
        exact False.elim ((List.mem_nil_iff entry).mp member)
      · intro name
        constructor
        · intro member
          obtain ⟨entry, inEmpty, _⟩ := List.mem_map.mp member
          exact False.elim ((List.mem_nil_iff entry).mp inEmpty)
        · intro member
          exact False.elim ((List.mem_nil_iff name).mp member.2)
      · intro pair
        constructor
        · intro member
          exact False.elim ((List.mem_nil_iff pair).mp member)
        · intro member
          exact False.elim ((List.mem_nil_iff pair).mp member.2)
    | cons pair tail ih =>
      obtain ⟨key, member, canonical, typed, nameSupport, pairSupport⟩ := ih
      by_cases selected : pair ∈ wanted.seen
      · refine ⟨extend key [] pair, ?_, extend_canonical key [] pair,
          extend_typed key [] pair, ?_, ?_⟩
        · rw [List.foldr_cons]
          exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨key, member, rfl⟩))
        · intro name
          constructor
          · intro present
            rcases (extend_names key [] pair name).mp present with inEmpty | old
            · exact False.elim ((List.mem_nil_iff name).mp inEmpty)
            · exact (nameSupport name).mp old
          · intro present
            exact (extend_names key [] pair name).mpr (.inr ((nameSupport name).mpr present))
        · intro next
          constructor
          · intro present
            rcases (extend_seen key [] pair next).mp present with same | old
            · subst next
              exact ⟨selected, List.mem_cons.mpr (.inl rfl)⟩
            · obtain ⟨inWanted, inTail⟩ := (pairSupport next).mp old
              exact ⟨inWanted, List.mem_cons.mpr (.inr inTail)⟩
          · intro present
            obtain ⟨inWanted, inPool⟩ := present
            rcases List.mem_cons.mp inPool with same | inTail
            · exact (extend_seen key [] pair next).mpr (.inl same)
            · exact (extend_seen key [] pair next).mpr
                (.inr ((pairSupport next).mpr ⟨inWanted, inTail⟩))
      · refine ⟨key, ?_, canonical, typed, nameSupport, ?_⟩
        · rw [List.foldr_cons]
          exact List.mem_append.mpr (.inl member)
        · intro next
          constructor
          · intro present
            obtain ⟨inWanted, inTail⟩ := (pairSupport next).mp present
            exact ⟨inWanted, List.mem_cons.mpr (.inr inTail)⟩
          · intro present
            obtain ⟨inWanted, inPool⟩ := present
            rcases List.mem_cons.mp inPool with same | inTail
            · subst next
              exact False.elim (selected inWanted)
            · exact (pairSupport next).mpr ⟨inWanted, inTail⟩
  | cons name tail ih =>
    obtain ⟨key, member, canonical, typed, nameSupport, pairSupport⟩ := ih
    let anchor := MicroCFTA.IntersectSchedule.pair
      MicroCFTA.IntersectSchedule.Input.empty MicroCFTA.IntersectSchedule.Input.empty
    by_cases selected : name ∈ names wanted
    · let next := MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey.mk
        (extend key [name] anchor).free key.seen
      refine ⟨next, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.foldr_cons]
        exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨key, member, rfl⟩))
      · exact ⟨(extend_canonical key [name] anchor).1, canonical.2⟩
      · change Typed (extend key [name] anchor)
        exact extend_typed key [name] anchor
      · intro current
        constructor
        · intro present
          rcases (extend_names key [name] anchor current).mp present with inBound | old
          · rcases List.mem_cons.mp inBound with same | inEmpty
            · subst current
              exact ⟨selected, List.mem_cons.mpr (.inl rfl)⟩
            · exact False.elim ((List.mem_nil_iff current).mp inEmpty)
          · obtain ⟨inWanted, inTail⟩ := (nameSupport current).mp old
            exact ⟨inWanted, List.mem_cons.mpr (.inr inTail)⟩
        · intro present
          obtain ⟨inWanted, inPool⟩ := present
          rcases List.mem_cons.mp inPool with same | inTail
          · exact (extend_names key [name] anchor current).mpr
              (.inl (List.mem_cons.mpr (.inl same)))
          · exact (extend_names key [name] anchor current).mpr
              (.inr ((nameSupport current).mpr ⟨inWanted, inTail⟩))
      · exact pairSupport
    · refine ⟨key, ?_, canonical, typed, ?_, pairSupport⟩
      · rw [List.foldr_cons]
        exact List.mem_append.mpr (.inl member)
      · intro current
        constructor
        · intro present
          obtain ⟨inWanted, inTail⟩ := (nameSupport current).mp present
          exact ⟨inWanted, List.mem_cons.mpr (.inr inTail)⟩
        · intro present
          obtain ⟨inWanted, inPool⟩ := present
          rcases List.mem_cons.mp inPool with same | inTail
          · subst current
            exact False.elim (selected inWanted)
          · exact (nameSupport current).mpr ⟨inWanted, inTail⟩


/-- Characterizes the canonical typed descriptors in the original carrier. -/
theorem mem_originalDescriptorCarrier_iff {Symbol Guard : Type}
    (state : MicroCFTA.InternedConstructorTemplates.State Symbol Guard)
    (key : MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey) :
    key ∈ originalDescriptorCarrier state ↔
      MicroCFTA.IntersectionFlatMemoKeyDomain.Canonical key ∧ Typed key ∧
      (∀ name, name ∈ names key → name ∈ List.range state.nodes.next) ∧
      (∀ pair, pair ∈ key.seen →
        pair ∈ (MicroCFTA.SourceRecursiveIntersectionInputView.inventory state).flatMap
          (fun left =>
            (MicroCFTA.SourceRecursiveIntersectionInputView.inventory state).map
              (fun right => MicroCFTA.IntersectSchedule.pair left right))) := by
  let pairs := (MicroCFTA.SourceRecursiveIntersectionInputView.inventory state).flatMap
    (fun left => (MicroCFTA.SourceRecursiveIntersectionInputView.inventory state).map
      (fun right => MicroCFTA.IntersectSchedule.pair left right))
  let empty : MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey := ⟨[], []⟩
  let anchor := MicroCFTA.IntersectSchedule.pair
    MicroCFTA.IntersectSchedule.Input.empty MicroCFTA.IntersectSchedule.Input.empty
  let pairChoices := List.foldr
    (fun pair keys => keys ++ keys.map (fun key => extend key [] pair)) [empty] pairs
  change key ∈ List.foldr (fun name keys => keys ++ keys.map (fun key =>
    MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey.mk
      (extend key [name] anchor).free key.seen)) pairChoices (List.range state.nodes.next) ↔
    MicroCFTA.IntersectionFlatMemoKeyDomain.Canonical key ∧ Typed key ∧
      (∀ name, name ∈ names key → name ∈ List.range state.nodes.next) ∧
      (∀ pair, pair ∈ key.seen → pair ∈ pairs)
  constructor
  · intro member
    have pairSound : ∀ pool current, current ∈ List.foldr
        (fun pair keys => keys ++ keys.map (fun key => extend key [] pair)) [empty] pool →
        MicroCFTA.IntersectionFlatMemoKeyDomain.Canonical current ∧ Typed current ∧
          (∀ name, name ∈ names current → False) ∧
          (∀ pair, pair ∈ current.seen → pair ∈ pool) := by
      intro pool
      induction pool with
      | nil =>
        intro current present
        rw [List.foldr_nil] at present
        rcases List.mem_cons.mp present with same | absent
        · subst current
          refine ⟨⟨List.Pairwise.nil, List.Pairwise.nil⟩, ?_, ?_, ?_⟩
          · intro entry h; exact False.elim ((List.mem_nil_iff entry).mp h)
          · intro name h
            obtain ⟨entry, absent, _⟩ := List.mem_map.mp h
            exact (List.mem_nil_iff entry).mp absent
          · intro pair h; exact False.elim ((List.mem_nil_iff pair).mp h)
        · exact False.elim ((List.mem_nil_iff current).mp absent)
      | cons pair tail ih =>
        intro current present
        rw [List.foldr_cons] at present
        rcases List.mem_append.mp present with old | added
        · obtain ⟨canonical, typed, noNames, seen⟩ := ih current old
          exact ⟨canonical, typed, noNames,
            fun next h => List.mem_cons.mpr (.inr (seen next h))⟩
        · obtain ⟨previous, previousMember, same⟩ := List.mem_map.mp added
          subst current
          obtain ⟨canonical, typed, noNames, seen⟩ := ih previous previousMember
          refine ⟨extend_canonical previous [] pair, extend_typed previous [] pair, ?_, ?_⟩
          · intro name h
            rcases (extend_names previous [] pair name).mp h with absent | old
            · exact (List.mem_nil_iff name).mp absent
            · exact noNames name old
          · intro next h
            rcases (extend_seen previous [] pair next).mp h with same | old
            · exact List.mem_cons.mpr (.inl same)
            · exact List.mem_cons.mpr (.inr (seen next old))
    have nameSound : ∀ pool current, current ∈ List.foldr
        (fun name keys => keys ++ keys.map (fun key =>
          MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey.mk
            (extend key [name] anchor).free key.seen)) pairChoices pool →
        MicroCFTA.IntersectionFlatMemoKeyDomain.Canonical current ∧ Typed current ∧
          (∀ name, name ∈ names current → name ∈ pool) ∧
          (∀ pair, pair ∈ current.seen → pair ∈ pairs) := by
      intro pool
      induction pool with
      | nil =>
        intro current present
        rw [List.foldr_nil] at present
        obtain ⟨canonical, typed, noNames, seen⟩ := pairSound pairs current present
        exact ⟨canonical, typed, fun name h => False.elim (noNames name h), seen⟩
      | cons name tail ih =>
        intro current present
        rw [List.foldr_cons] at present
        rcases List.mem_append.mp present with old | added
        · obtain ⟨canonical, typed, bounded, seen⟩ := ih current old
          exact ⟨canonical, typed,
            fun next h => List.mem_cons.mpr (.inr (bounded next h)), seen⟩
        · obtain ⟨previous, previousMember, same⟩ := List.mem_map.mp added
          subst current
          obtain ⟨canonical, typed, bounded, seen⟩ := ih previous previousMember
          refine ⟨⟨(extend_canonical previous [name] anchor).1, canonical.2⟩,
            extend_typed previous [name] anchor, ?_, seen⟩
          intro next h
          rcases (extend_names previous [name] anchor next).mp h with bound | old
          · rcases List.mem_cons.mp bound with same | absent
            · exact List.mem_cons.mpr (.inl same)
            · exact False.elim ((List.mem_nil_iff next).mp absent)
          · exact List.mem_cons.mpr (.inr (bounded next old))
    exact nameSound (List.range state.nodes.next) key member
  · intro bounded
    obtain ⟨canonical, typed, boundedNames, boundedSeen⟩ := bounded
    obtain ⟨other, member, otherCanonical, otherTyped, sameNames, sameSeen⟩ :=
      choice_fields_witness (List.range state.nodes.next) pairs key
    have nameEq : ∀ name, name ∈ names other ↔ name ∈ names key := by
      intro name
      exact ⟨fun h => ((sameNames name).mp h).1,
        fun h => (sameNames name).mpr ⟨h, boundedNames name h⟩⟩
    have freeEq : ∀ binding, binding ∈ other.free ↔ binding ∈ key.free := by
      intro binding
      obtain ⟨name, reference⟩ := binding
      constructor
      · intro present
        have referenceEq := otherTyped (name, reference) present
        have nameMember : name ∈ names other :=
          List.mem_map.mpr ⟨(name, reference), present, rfl⟩
        obtain ⟨⟨foundName, foundRef⟩, foundMember, sameName⟩ :=
          List.mem_map.mp ((nameEq name).mp nameMember)
        dsimp only at sameName
        subst foundName
        have foundEq : (name, foundRef) = (name, reference) := by
          rw [show foundRef = _ from typed (name, foundRef) foundMember,
            show reference = _ from referenceEq]
        exact foundEq ▸ foundMember
      · intro present
        have referenceEq := typed (name, reference) present
        have nameMember : name ∈ names key :=
          List.mem_map.mpr ⟨(name, reference), present, rfl⟩
        obtain ⟨⟨foundName, foundRef⟩, foundMember, sameName⟩ :=
          List.mem_map.mp ((nameEq name).mpr nameMember)
        dsimp only at sameName
        subst foundName
        have foundEq : (name, foundRef) = (name, reference) := by
          rw [show foundRef = _ from otherTyped (name, foundRef) foundMember,
            show reference = _ from referenceEq]
        exact foundEq ▸ foundMember
    have seenEq : ∀ pair, pair ∈ other.seen ↔ pair ∈ key.seen := by
      intro pair
      exact ⟨fun h => ((sameSeen pair).mp h).1,
        fun h => (sameSeen pair).mpr ⟨h, boundedSeen pair h⟩⟩
    have same : other = key :=
      (MicroCFTA.IntersectionFlatMemoKeyDomain.canonical_eq_iff
        other key otherCanonical canonical).mpr ⟨freeEq, seenEq⟩
    exact same ▸ member


/-- Preserves the carrier under an extension with original inputs. -/
theorem extend_mem_originalDescriptorCarrier {Symbol Guard : Type}
    (state : MicroCFTA.InternedConstructorTemplates.State Symbol Guard)
    (facts : MicroCFTA.InternedNestedFacts.Facts state)
    (key : MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey)
    (bound : List Nat)
    (left right : MicroCFTA.IntersectSchedule.Input)
    (member : key ∈ originalDescriptorCarrier state)
    (leftOriginal : MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput state left)
    (rightOriginal : MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput state right)
    (boundOriginal : ∀ name, name ∈ bound →
      MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput state
        (MicroCFTA.IntersectSchedule.Input.mu name)) :
    extend key bound (MicroCFTA.IntersectSchedule.pair left right) ∈
      originalDescriptorCarrier state := by
  obtain ⟨_, _, namesBound, seenBound⟩ :=
    (mem_originalDescriptorCarrier_iff state key).mp member
  refine (mem_originalDescriptorCarrier_iff state
    (extend key bound (MicroCFTA.IntersectSchedule.pair left right))).mpr ?_
  refine ⟨extend_canonical key bound (MicroCFTA.IntersectSchedule.pair left right),
    extend_typed key bound (MicroCFTA.IntersectSchedule.pair left right), ?_, ?_⟩
  · intro name extended
    rcases (extend_names key bound (MicroCFTA.IntersectSchedule.pair left right) name).mp
      extended with fromBound | fromOld
    · exact MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput.mu_inventory_name
        state facts name (boundOriginal name fromBound)
    · exact namesBound name fromOld
  · intro pair extended
    rcases (extend_seen key bound (MicroCFTA.IntersectSchedule.pair left right) pair).mp
      extended with same | fromOld
    · subst pair
      exact List.mem_flatMap.mpr ⟨left,
        MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput.inventory
          state facts left leftOriginal,
        List.mem_map.mpr ⟨right,
          MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput.inventory
            state facts right rightOriginal, rfl⟩⟩
    · exact seenBound pair fromOld

end MicroCFTA.SourceRecursiveIntersectionDomain
