local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- A stored value has a graph restriction or its completed fragment. -/
def GraphValue : UVarValue Symbol → Prop
  | .unenumerated (some _) _ | .enumerated _ => True
  | _ => False

/-- A variable's class contains a stored graph restriction or completed fragment. -/
def CarriesGraph (state : State Symbol Guard) (uv : Nat) : Prop :=
  ∃ held value, UnionFind.SameClass state.representatives uv held ∧ state.values[held]? = some value ∧ GraphValue value

/-- An action retains each existing graph-bearing equality class. -/
def PreservesCarriers (before after : State Symbol Guard) : Prop :=
  ∀ uv, CarriesGraph before uv → CarriesGraph after uv

/-- Carrier preservation composes across consecutive actual states. -/
theorem PreservesCarriers.trans (first : PreservesCarriers before middle) (second : PreservesCarriers middle after) :
    PreservesCarriers before after := fun uv carried => second uv (first uv carried)

/-- An unchanged state preserves every carrier. -/
theorem PreservesCarriers.refl (state : State Symbol Guard) : PreservesCarriers state state := fun _ carried => carried

/-- A graph-bearing slot supplies a carrier for every variable in its class. -/
theorem carries_stored (state : State Symbol Guard) (uv held : Nat) (value : UVarValue Symbol)
    (same : UnionFind.SameClass state.representatives uv held) (stored : state.values[held]? = some value) (graph : GraphValue value) :
    CarriesGraph state uv := ⟨held, value, same, stored, graph⟩

/-- A total forest makes each graph-bearing slot its own carrier. -/
theorem carries_self (state : State Symbol Guard) (total : UnionFind.Total state.representatives) (uv : Nat) (value : UVarValue Symbol)
    (stored : state.values[uv]? = some value) (graph : GraphValue value) : CarriesGraph state uv := by
  obtain ⟨root, size, path⟩ := total uv
  exact ⟨uv, value, ⟨root, size, path, path⟩, stored, graph⟩

/-- Enlarging classes and retaining values preserves graph carriers. -/
theorem carriers_classes (before after : State Symbol Guard) (values : after.values = before.values)
    (classes : ∀ left right, UnionFind.SameClass before.representatives left right → UnionFind.SameClass after.representatives left right) :
    PreservesCarriers before after := by
  rintro uv ⟨held, value, same, stored, graph⟩
  exact ⟨held, value, classes uv held same, by simpa [values] using stored, graph⟩

/-- Actual representative lookup preserves every graph carrier. -/
theorem representative_carriers (fuel uv root : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives) (success : Success (representative fuel uv) before root after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after := by
  obtain ⟨found, lookup, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact ⟨UnionFind.findRoot_total total lookup, carriers_classes _ _ rfl
    (fun left right same => (UnionFind.findRoot_classes total lookup left right).mpr same)⟩

/-- Actual equality union preserves every graph carrier. -/
theorem union_carriers (fuel left right : Nat) (before after : State Symbol Guard)
    (total : UnionFind.Total before.representatives) (success : Success (unionVariables fuel left right) before () after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after := by
  obtain ⟨forest, lookup, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact ⟨(UnionFind.union_correct total lookup).1, carriers_classes _ _ rfl
    (fun left right same => ((UnionFind.union_correct total lookup).2 left right).mpr (Or.inl same))⟩

/-- Fresh allocation retains every earlier graph carrier. -/
theorem allocation_carriers (node : Option Nat) (before : State Symbol Guard) : PreservesCarriers before (allocated node before) := by
  rintro uv ⟨held, value, same, stored, graph⟩
  have inside := (List.getElem?_eq_some_iff.mp stored).1
  exact ⟨held, value, same, by simpa [allocated, List.getElem?_append, inside] using stored, graph⟩

/-- Replacing a stored graph-bearing value by another retains every carrier. -/
theorem set_graph_carriers (before : State Symbol Guard) (uv : Nat) (value : UVarValue Symbol) (graph : GraphValue value) :
    PreservesCarriers before {before with values := before.values.set uv value} := by
  rintro other ⟨held, old, same, stored, oldGraph⟩
  by_cases selected : held = uv
  · subst held
    have inside := (List.getElem?_eq_some_iff.mp stored).1
    exact ⟨uv, value, same, by simp [inside], graph⟩
  · exact ⟨held, old, same, by simpa [Ne.symm selected] using stored, oldGraph⟩

/-- Pending-value intersection retains either operand's graph restriction. -/
theorem intersection_graph (graph : Graph Symbol Guard) (left right merged : UVarValue Symbol)
    (intersection : intersectValues graph left right = some merged) (bearing : GraphValue left ∨ GraphValue right) : GraphValue merged := by
  cases left <;> cases right <;> simp only [intersectValues] at intersection
