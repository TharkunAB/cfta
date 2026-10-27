/-- Interpret one concrete source slot as the previously verified fragment-domain slot. -/
def slot (language : NodeLanguage Symbol) : UVarValue Symbol → Slot Symbol
  | .unenumerated node scs =>
      .pending (node.map language) (scs.map fun sc => fun assignment term => Suspended.Holds assignment term sc)
  | .enumerated fragment => .expanded fragment
  | .eliminated => .eliminated

/-- Missing array positions impose no term restriction; operations still report invalid accesses. -/
def heap (language : NodeLanguage Symbol) (values : List (UVarValue Symbol)) : Heap Symbol :=
  fun uv => slot language (values[uv]?.getD .eliminated)

/-- Retained residual guards apply to their completed guarded fragments. -/
def guardsHold (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (obligations : List (Guard × Fragment Symbol)) : Prop :=
  ∀ obligation ∈ obligations, meaning obligation.1 (fill assignment obligation.2)

/-- A complete assignment satisfies all forest equalities, stored slots, and retained guards. -/
def Satisfies (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (state : State Symbol Guard) : Prop :=
  Fragments.stateSatisfies state.representatives (heap language state.values) assignment ∧
    guardsHold meaning assignment state.obligations

/-- An empty slot array imposes no restriction. -/
theorem heap_empty (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) :
    heapSatisfies (heap language []) assignment := by
  intro uv
  simp [heap, slot, slotSatisfies]

/-- The slot array and allocator identify the same finite domain. -/
def SupplyAligned (state : State Symbol Guard) : Prop := state.counter = state.values.length

/-- A successful representative lookup has exactly the source state update. -/
theorem representative_exact (fuel uv : Nat) (state : State Symbol Guard) (found : UnionFind.Result)
    (result : UnionFind.findRoot fuel state.representatives uv = some found) :
    representative fuel uv state = [.ok (found.representative, {state with representatives := found.forest})] := by
  simp [representative, result, bind, get, getThe, MonadStateOf.get, set, pure,
    StateT.bind, StateT.pure, StateT.get, StateT.set, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk]

/-- The actual representative action preserves exactly every complete assignment. -/
theorem representative_semantics (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv : Nat) (state : State Symbol Guard) (found : UnionFind.Result)
    (valid : UnionFind.Total state.representatives)
    (result : UnionFind.findRoot fuel state.representatives uv = some found) :
    Satisfies language meaning assignment {state with representatives := found.forest} ↔
      Satisfies language meaning assignment state := by
  simp only [Satisfies, Fragments.stateSatisfies, UnionFind.findRoot_satisfies valid result]
