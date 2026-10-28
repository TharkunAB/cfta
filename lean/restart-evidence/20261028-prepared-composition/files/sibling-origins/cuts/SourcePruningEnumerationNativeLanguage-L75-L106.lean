    (beforeHeap afterHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : EnumerationState.State Symbol EnumGuard)
    (realized : PendingRealized beforeHeap state)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap) :
    heap (handles holds ambient afterHeap) state.values = heap (handles holds ambient beforeHeap) state.values := by
  funext uv
  unfold heap
  cases stored : state.values[uv]? with
  | none => rfl
  | some value => exact slot_keeps holds ambient beforeHeap afterHeap state uv value stored realized kept

/-- Complete assignment meaning is unchanged for the old realized state under native growth. -/
theorem satisfies_keeps
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (beforeHeap afterHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : EnumerationState.State Symbol EnumGuard)
    (residualMeaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (realized : PendingRealized beforeHeap state)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap) :
    Satisfies (handles holds ambient afterHeap) residualMeaning assignment state ↔
      Satisfies (handles holds ambient beforeHeap) residualMeaning assignment state := by
  unfold Satisfies
  rw [heap_keeps holds ambient beforeHeap afterHeap state realized kept]

/-- An enumeration frame retains the exact finite equivalence classes without a safety premise. -/
theorem frame_sameClass (before after : EnumerationState.State Symbol EnumGuard)
    (frame : Frame before after) (left right : Nat) :
    UnionFind.SameClass after.representatives left right ↔
      UnionFind.SameClass before.representatives left right := by
  constructor
  · rintro ⟨root, size, leftPath, rightPath⟩
    exact ⟨root, size, (frame.reaches left root size).mp leftPath,
