import MicroCFTA.InternedValueMassConstructors
import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedNestedConstructionGrowth

/-!
# Causal payload bounds for full repaired source construction

The original syntax transforms an initial bound on captured values and all
stored payloads. Every actual stopping state retains the transformed store
bound. Warm first-writer values use that same causal store invariant.
-/
namespace MicroCFTA.InternedFreshOrdinaryResultMass
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges ordinaryLevel)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "mass" => InternedValueMass.value
local notation "edgeMass" => InternedValueMass.edge
variable {Symbol Guard : Type}

/-- One constructor pays for its literal list and retains the earlier store. -/
def inflate (length bound : Nat) : Nat := max bound (1 + length * (1 + bound))

/-- Constructor bounds retain every earlier payload bound. -/
theorem inflate_ge (length bound : Nat) : bound ≤ inflate length bound := Nat.le_max_left _ _

/-- A larger initial bound supports the same literal constructor list. -/
theorem inflate_mono (length : Nat) {first last : Nat} (enough : first ≤ last) :
    inflate length first ≤ inflate length last := by
  have multiplied := Nat.mul_le_mul_left length (Nat.add_le_add_left enough 1)
  unfold inflate
  omega

mutual
/-- Compute a complete source payload bound from original syntax and initial stores. -/
def transform : Syntax Symbol Guard → Nat → Nat
  | .empty, bound | .var _, bound => bound
  | .node rows, bound => inflate rows.length (rowsTransform rows bound)
  | .union values, bound => inflate values.length (manyTransform values bound)
  | .binder _ body, bound =>
      let depth := transform body bound
      let ordinary := transform body depth
      let actual := transform body ordinary
      1 + 3 * actual
termination_by expression => sizeOf expression

/-- Source children execute in order, with each actual prefix's transformed store. -/
def manyTransform : List (Syntax Symbol Guard) → Nat → Nat
  | [], bound => bound
  | first :: rest, bound => manyTransform rest (transform first bound)
termination_by expressions => sizeOf expressions

/-- Each row constructs children, emits one edge, then executes its tail. -/
def rowsTransform : List (EdgeSyntax Symbol Guard) → Nat → Nat
  | [], bound => bound
  | .mk _ _ children :: rest, bound =>
      rowsTransform rest (inflate children.length (manyTransform children bound))
termination_by expressions => sizeOf expressions
end

mutual
/-- Every full syntax transformer retains its initial bound. -/
theorem transform_ge (expression : Syntax Symbol Guard) (bound : Nat) : bound ≤ transform expression bound := by
  cases expression with
  | empty | var => simp only [transform]; exact Nat.le_refl _
  | node rows => rw [transform]; exact Nat.le_trans (rowsTransform_ge rows bound) (inflate_ge _ _)
  | union values => rw [transform]; exact Nat.le_trans (manyTransform_ge values bound) (inflate_ge _ _)
  | binder smart body =>
      have first := transform_ge body bound
      have second := transform_ge body (transform body bound)
      have third := transform_ge body (transform body (transform body bound))
      simp only [transform]
      omega
termination_by sizeOf expression

/-- An ordered source list retains its initial bound. -/
theorem manyTransform_ge (expressions : List (Syntax Symbol Guard)) (bound : Nat) : bound ≤ manyTransform expressions bound := by
  cases expressions with
  | nil => rw [manyTransform]; exact Nat.le_refl _
  | cons first rest => rw [manyTransform]; exact Nat.le_trans (transform_ge first bound) (manyTransform_ge rest _)
termination_by sizeOf expressions

/-- An ordered row list retains its initial bound. -/
theorem rowsTransform_ge (expressions : List (EdgeSyntax Symbol Guard)) (bound : Nat) : bound ≤ rowsTransform expressions bound := by
  cases expressions with
  | nil => rw [rowsTransform]; exact Nat.le_refl _
  | cons first rest =>
      cases first
      rw [rowsTransform]
      exact Nat.le_trans (manyTransform_ge _ bound) (Nat.le_trans (inflate_ge _ _) (rowsTransform_ge rest _))
termination_by sizeOf expressions
end

mutual
/-- Full source bounds are monotone in the initial store and capture bound. -/
theorem transform_mono (expression : Syntax Symbol Guard) {first last : Nat} (enough : first ≤ last) :
    transform expression first ≤ transform expression last := by
  cases expression with
  | empty | var => simpa only [transform] using enough
  | node rows => simpa only [transform] using inflate_mono rows.length (rowsTransform_mono rows enough)
  | union values => simpa only [transform] using inflate_mono values.length (manyTransform_mono values enough)
  | binder smart body =>
      have bound := transform_mono body (transform_mono body (transform_mono body enough))
      simp only [transform]
      omega
termination_by sizeOf expression

/-- The ordered child transformer is monotone. -/
theorem manyTransform_mono (expressions : List (Syntax Symbol Guard)) {first last : Nat} (enough : first ≤ last) :
    manyTransform expressions first ≤ manyTransform expressions last := by
  cases expressions with
  | nil => simpa only [manyTransform] using enough
  | cons value rest => simpa only [manyTransform] using manyTransform_mono rest (transform_mono value enough)
termination_by sizeOf expressions

/-- The ordered row transformer is monotone. -/
theorem rowsTransform_mono (expressions : List (EdgeSyntax Symbol Guard)) {first last : Nat} (enough : first ≤ last) :
    rowsTransform expressions first ≤ rowsTransform expressions last := by
  cases expressions with
  | nil => simpa only [rowsTransform] using enough
  | cons value rest =>
      cases value
      simpa only [rowsTransform] using rowsTransform_mono rest (inflate_mono _ (manyTransform_mono _ enough))
termination_by sizeOf expressions
end

private theorem values_le (values : List (Value Symbol Guard)) (bound : Nat)
    (inputs : ∀ value ∈ values, mass value ≤ bound) :
    InternedValueMass.values values ≤ values.length * (1 + bound) := by
  induction values with
  | nil => simp only [InternedValueMass.values, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons first rest ih =>
      have own := inputs first List.mem_cons_self
      have tail := ih (fun value member => inputs value (List.mem_cons_of_mem _ member))
      simp only [InternedValueMass.values, List.length_cons, Nat.succ_mul]
      omega

private theorem edges_le (edges : List (EdgeValue Symbol Guard)) (bound : Nat)
    (inputs : ∀ edge ∈ edges, edgeMass edge ≤ bound) :
    InternedValueMass.edges edges ≤ edges.length * (1 + bound) := by
  induction edges with
  | nil => simp only [InternedValueMass.edges, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons first rest ih =>
      have own := inputs first List.mem_cons_self
      have tail := ih (fun edge member => inputs edge (List.mem_cons_of_mem _ member))
      simp only [InternedValueMass.edges, List.length_cons, Nat.succ_mul]
      omega

private abbrev Checked (bound : Nat) (outcome : Outcome Symbol Guard A) (post : A → Prop) : Prop :=
  Stored bound outcome.state ∧ ∀ value state, outcome = .done value state → post value

private theorem done_checked (bound : Nat) (value : A) (state : State Symbol Guard)
    (post : A → Prop) (stored : Stored bound state) (result : post value) : Checked bound (.done value state) post := by
  refine ⟨stored, ?_⟩
  intro other after same
  cases same
  exact result

private theorem bind_checked (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B) (firstBound lastBound : Nat)
    (firstPost : A → Prop) (post : B → Prop) (enough : firstBound ≤ lastBound)
    (first : Checked firstBound outcome firstPost)
    (later : ∀ value state, Stored firstBound state → firstPost value → Checked lastBound (next value state) post) :
    Checked lastBound (outcome.bind next) post := by
  cases outcome with
  | pending key state =>
      refine ⟨first.1.mono enough, ?_⟩
      intro value after impossible
      cases impossible
  | done value state => exact later value state first.1 (first.2 value state rfl)

section Construction
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem node_checked (rows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (bound : Nat)
    (stored : Stored bound state) (inputs : ∀ row ∈ rows, edgeMass row ≤ bound) :
    Checked (inflate rows.length bound) (work (makeNode rows) state) (fun result => mass result ≤ inflate rows.length bound) := by
  have raw := InternedValueMassConstructors.node rows state stored
  have listBound := edges_le rows bound inputs
  have enough : max bound (1 + InternedValueMass.edges rows) ≤ inflate rows.length bound :=
    by unfold inflate; omega
  exact done_checked _ _ _ _ (raw.1.mono enough) (Nat.le_trans raw.2 enough)

private theorem edge_checked (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (bound : Nat) (stored : Stored bound state)
    (inputs : ∀ value ∈ values, mass value ≤ bound) :
    Checked (inflate values.length bound) (work (makeEdge symbol guard values) state)
      (fun result => edgeMass result ≤ inflate values.length bound) := by
  have raw := InternedValueMassConstructors.edge symbol guard values state stored
  have listBound := values_le values bound inputs
  have enough : max bound (1 + InternedValueMass.values values) ≤ inflate values.length bound :=
    by unfold inflate; omega
  exact done_checked _ _ _ _ (raw.1.mono enough) (Nat.le_trans raw.2 enough)

private theorem union_checked (values : List (Value Symbol Guard)) (state : State Symbol Guard) (bound : Nat)
    (stored : Stored bound state) (inputs : ∀ value ∈ values, mass value ≤ bound) :
    Checked (inflate values.length bound) (work (makeUnion values) state) (fun result => mass result ≤ inflate values.length bound) := by
  have raw := InternedValueMassConstructors.union values state stored
  have listBound := values_le values bound inputs
  have enough : max bound (1 + InternedValueMass.values values) ≤ inflate values.length bound :=
    by unfold inflate; omega
  exact done_checked _ _ _ _ (raw.1.mono enough) (Nat.le_trans raw.2 enough)

private theorem finish_le (smart : Bool) (value : Value Symbol Guard) : mass (finish smart value) ≤ mass value := by
  unfold finish
  split
  · exact InternedValueMassConstructors.cleanup_le value
  · exact Nat.le_refl _

private theorem request_checked (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (bound returned : Nat) (stored : Stored bound state)
    (depthBound : mass depth ≤ bound) (ordinaryBound : mass ordinary ≤ bound) (enough : bound ≤ returned)
    (callbacks : ∀ name current, Stored bound current → Checked returned (callback name current) (fun value => mass value ≤ returned)) :
    Checked (1 + 3 * returned) (request smart depth ordinary callback state)
      (fun result => mass result ≤ 1 + 3 * returned) := by
  have oldEnough : bound ≤ 1 + 3 * returned := by omega
  unfold request
  dsimp only
  split
  · rename_i entry present
    split
    · rename_i result found
      apply done_checked _ _ _ _ (stored.mono oldEnough)
      have valueBound := stored.nodes _ _ found
      exact Nat.le_trans (finish_le smart result) (by omega)
    · refine ⟨stored.mono oldEnough, ?_⟩
      intro value after impossible
      cases impossible
  · let selected := Cache.intern state.nodes (muKey depth ordinary)
    let reserved : State Symbol Guard := {state with nodes := selected.2}
    have reservedStored : Stored bound reserved := ⟨stored.positive, stored.nodes, stored.edges⟩
    have body := callbacks (.interned selected.1.identity) reserved reservedStored
    change Checked (1 + 3 * returned)
      ((callback (.interned selected.1.identity) reserved).bind fun value after =>
        .done (finish smart (((keepFirst after.nodeRecords (muKey depth ordinary) (.mu selected.1 value depth ordinary))
          (muKey depth ordinary)).getD (.mu selected.1 value depth ordinary)))
          {after with nodeRecords := keepFirst after.nodeRecords (muKey depth ordinary) (.mu selected.1 value depth ordinary)}) _
    apply bind_checked _ _ returned _ _ _ (by omega) body
    intro value after afterStored valueBound
    let key := muKey depth ordinary
    let candidate : Value Symbol Guard := .mu selected.1 value depth ordinary
    have candidateBound : mass candidate ≤ 1 + 3 * returned := by
      simp only [candidate, InternedValueMass.value]
      omega
    have installed : Stored (1 + 3 * returned)
        {after with nodeRecords := keepFirst after.nodeRecords key candidate} := by
      refine ⟨by omega, ?_, ?_⟩
      · intro other payload found
        cases existing : after.nodeRecords key with
        | some old =>
            exact Nat.le_trans (afterStored.nodes other payload (by simpa only [keepFirst, existing] using found)) (by omega)
        | none =>
            by_cases same : other = key
            · subst other
              have identical : candidate = payload := by simpa only [keepFirst, existing, put, ite_true] using found
              exact identical ▸ candidateBound
            · exact Nat.le_trans (afterStored.nodes other payload (by
                simpa only [keepFirst, existing, put, ite_eq_right same] using found)) (by omega)
      · intro other payload found
        exact Nat.le_trans (afterStored.edges other payload found) (by omega)
    apply done_checked _ _ _ _ installed
    cases found : after.nodeRecords key with
    | some old =>
        have oldBound := afterStored.nodes key old found
        simpa only [keepFirst, found, Option.getD_some] using Nat.le_trans (finish_le smart old) (by omega : mass old ≤ 1 + 3 * returned)
    | none =>
        simpa only [keepFirst, found, put, ite_true, Option.getD_some] using Nat.le_trans (finish_le smart candidate) candidateBound

mutual
/-- Every full actual source outcome retains a causal store and bounds each returned value. -/
theorem build_bound (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (bound : Nat) (stored : Stored bound state)
    (inputs : ∀ value ∈ environment, mass value ≤ bound) :
    Stored (transform expression bound) (build expression environment state).state ∧
      ∀ value after, build expression environment state = .done value after → mass value ≤ transform expression bound := by
  cases expression with
  | empty =>
      rw [build, transform]
      exact done_checked _ _ _ _ stored (by simpa only [InternedValueMass.value] using stored.positive)
  | var index =>
      rw [build, transform]
      apply done_checked _ _ _ _ stored
      cases found : environment[index]? with
      | none => simpa only [Option.getD_none, InternedValueMass.value] using stored.positive
      | some value => exact inputs value (List.mem_of_getElem? found)
  | node rows =>
      rw [build, transform]
      apply bind_checked _ _ (rowsTransform rows bound) _ _ _ (inflate_ge _ _) (buildEdges_bound rows environment state bound stored inputs)
      intro values after afterStored bounded
      have result := node_checked values after _ afterStored bounded.2
      simpa only [bounded.1] using result
  | union members =>
      rw [build, transform]
      apply bind_checked _ _ (manyTransform members bound) _ _ _ (inflate_ge _ _) (buildMany_bound members environment state bound stored inputs)
      intro values after afterStored bounded
      have result := union_checked values after _ afterStored bounded.2
      simpa only [bounded.1] using result
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value after => work (withoutSelfReference name value) after
      have callbackBound : ∀ name current currentBound, Stored currentBound current → bound ≤ currentBound →
          Checked (transform body currentBound) (callback name current) (fun value => mass value ≤ transform body currentBound) := by
        intro name current currentBound currentStored grows
        have extended : ∀ value ∈ Value.reference name :: environment, mass value ≤ currentBound := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [InternedValueMass.value] using currentStored.positive
          · exact Nat.le_trans (inputs value member) grows
        apply bind_checked _ _ (transform body currentBound) _ _ _ (Nat.le_refl _) (build_bound body _ current currentBound currentStored extended)
        intro value after afterStored valueBound
        have filtered := InternedValueMassConstructors.filter name value after afterStored valueBound
        exact done_checked _ _ _ _ filtered.1 filtered.2
      let depthBound := transform body bound
      let ordinaryBound := transform body depthBound
      let actualBound := transform body ordinaryBound
      have firstLe : bound ≤ depthBound := transform_ge body bound
      have secondLe : depthBound ≤ ordinaryBound := transform_ge body depthBound
      have thirdLe : ordinaryBound ≤ actualBound := transform_ge body ordinaryBound
      rw [build, transform]
      change Checked (1 + 3 * actualBound)
        ((callback .depth state).bind fun depth afterDepth =>
          (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
            request smart depth ordinary callback afterOrdinary) _
      apply bind_checked _ _ depthBound _ _ _ (by omega) (callbackBound .depth state bound stored (Nat.le_refl _))
      intro depth afterDepth depthStored depthSize
      apply bind_checked _ _ ordinaryBound _ _ _ (by omega) (callbackBound _ afterDepth depthBound depthStored firstLe)
      intro ordinary afterOrdinary ordinaryStored ordinarySize
      exact request_checked smart depth ordinary callback afterOrdinary ordinaryBound actualBound ordinaryStored
        (by omega) ordinarySize thirdLe (fun name current currentStored => callbackBound name current ordinaryBound currentStored (by omega))
termination_by sizeOf expression

/-- Ordered children retain exact length, causal stores, and a bound at every original result position. -/
theorem buildMany_bound (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (bound : Nat) (stored : Stored bound state)
    (inputs : ∀ value ∈ environment, mass value ≤ bound) :
    Stored (manyTransform expressions bound) (buildMany expressions environment state).state ∧
      ∀ values after, buildMany expressions environment state = .done values after →
        values.length = expressions.length ∧ ∀ value ∈ values, mass value ≤ manyTransform expressions bound := by
  cases expressions with
  | nil =>
      rw [buildMany, manyTransform]
      exact done_checked _ _ _ _ stored ⟨rfl, by intro value member; cases member⟩
  | cons first rest =>
      rw [buildMany, manyTransform]
      apply bind_checked _ _ (transform first bound) _ _ _ (manyTransform_ge _ _) (build_bound first environment state bound stored inputs)
      intro value after afterStored valueSize
      have nextInputs : ∀ value ∈ environment, mass value ≤ transform first bound :=
        fun value member => Nat.le_trans (inputs value member) (transform_ge first bound)
      apply bind_checked _ _ (manyTransform rest (transform first bound)) _ _ _ (Nat.le_refl _)
        (buildMany_bound rest environment after _ afterStored nextInputs)
      intro values final finalStored bounded
      apply done_checked _ _ _ _ finalStored
      refine ⟨by simp only [List.length_cons, bounded.1], ?_⟩
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_trans valueSize (manyTransform_ge _ _)
      · exact bounded.2 result member
termination_by sizeOf expressions

/-- Ordered rows retain exact length and each actual returned edge's full payload bound. -/
theorem buildEdges_bound (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (bound : Nat) (stored : Stored bound state)
    (inputs : ∀ value ∈ environment, mass value ≤ bound) :
    Stored (rowsTransform expressions bound) (buildEdges expressions environment state).state ∧
      ∀ values after, buildEdges expressions environment state = .done values after →
        values.length = expressions.length ∧ ∀ value ∈ values, edgeMass value ≤ rowsTransform expressions bound := by
  cases expressions with
  | nil =>
      rw [buildEdges, rowsTransform]
      exact done_checked _ _ _ _ stored ⟨rfl, by intro value member; cases member⟩
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [buildEdges, rowsTransform]
          have enough := Nat.le_trans (inflate_ge children.length (manyTransform children bound)) (rowsTransform_ge rest _)
          apply bind_checked _ _ (manyTransform children bound) _ _ _ enough (buildMany_bound children environment state bound stored inputs)
          intro values after afterStored bounded
          have edgeChecked := edge_checked symbol guard values after _ afterStored bounded.2
          rw [bounded.1] at edgeChecked
          apply bind_checked _ _ (inflate children.length (manyTransform children bound)) _ _ _ (rowsTransform_ge rest _) edgeChecked
          intro row afterEdge edgeStored rowSize
          have nextInputs : ∀ value ∈ environment, mass value ≤ inflate children.length (manyTransform children bound) :=
            fun value member => Nat.le_trans (inputs value member)
              (Nat.le_trans (manyTransform_ge children bound) (inflate_ge _ _))
          apply bind_checked _ _ (rowsTransform rest (inflate children.length (manyTransform children bound))) _ _ _ (Nat.le_refl _)
            (buildEdges_bound rest environment afterEdge _ edgeStored nextInputs)
          intro rows final finalStored restBound
          apply done_checked _ _ _ _ finalStored
          refine ⟨by simp only [List.length_cons, restBound.1], ?_⟩
          intro result member
          rcases List.mem_cons.mp member with rfl | member
          · exact Nat.le_trans rowSize (rowsTransform_ge rest _)
          · exact restBound.2 result member
termination_by sizeOf expressions
end
end Construction
end MicroCFTA.InternedFreshOrdinaryResultMass
