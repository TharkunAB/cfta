import MicroCFTA.ConstructorProbeWorklist

/-!
# Root contexts and productive transition probes

The source extends a stored context at every child position of every usable
transition. Fixed witnesses fill all other positions.
-/
namespace MicroCFTA.ConstructorProbeContexts
open Language Cache ConstructorProbeWitnesses
variable {State Symbol : Type}

/-- The generated source closure has one hole and a finite stack of constructor frames. -/
inductive Context (Symbol : Type) where
  | hole
  | frame (outer : Context Symbol) (symbol : Symbol) (arguments : List (Term Symbol)) (position : Nat)

/-- Apply the exact source adjustAt replacement, then apply the previous context. -/
def plug : Context Symbol → Term Symbol → Term Symbol
  | .hole, term => term
  | .frame outer symbol terms position, term => plug outer (.node symbol (terms.set position term))

/-- A context turns every admitted hole term into an admitted initial-state term. -/
def Fits (rows : Rows State Symbol) (root state : State) (context : Context Symbol) : Prop :=
  ∀ term, Admits rows state term → Admits rows root (plug context term)

/-- Child-position enumeration retains the exact indexed child state. -/
theorem position_exact (children : List State) (state : State) (position : Nat) :
    (state, position) ∈ children.zipIdx ↔ children[position]? = some state := by
  constructor
  · intro member
    obtain ⟨_, bound, same⟩ := List.mem_zipIdx member
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨by simpa using bound, by simpa using same.symm⟩
  · intro found
    obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
    apply List.mem_iff_getElem.mpr
    refine ⟨position, by simpa using bound, ?_⟩
    simp [List.getElem_zipIdx, same]

/-- Replacing a selected child's term preserves the ordered accepting forest. -/
theorem forest_replace (rows : Rows State Symbol) (children : List State) (terms : List (Term Symbol))
    (accepted : All₂ (Admits rows) children terms) (position : Nat) (state : State)
    (found : children[position]? = some state) (replacement : Term Symbol) (valid : Admits rows state replacement) :
    All₂ (Admits rows) children (terms.set position replacement) := by
  induction accepted generalizing position with
  | nil => simp at found
  | cons first rest ih =>
      cases position with
      | zero =>
          have same := Option.some.inj found
          subst state
          exact .cons valid rest
      | succ position =>
          exact .cons first (ih position (by simpa using found))

/-- A successful child lookup returns an admitted forest of the selected witnesses. -/
theorem witness_arguments (rows : Rows (Fin count) Symbol) (children : List (Fin count)) (terms : List (Term Symbol))
    (found : arguments (witnesses rows) children = some terms) : All₂ (Admits rows) children terms :=
  All₂.imp (witnesses_sound rows) ((arguments_exact _ _ _).mp found)

/-- If each child language is inhabited, the actual selected-witness traversal succeeds. -/
theorem arguments_available (rows : Rows (Fin count) Symbol) (children : List (Fin count))
    (inhabited : ∀ child ∈ children, ∃ term, Admits rows child term) :
    ∃ terms, arguments (witnesses rows) children = some terms := by
  obtain ⟨terms, related⟩ := Productivity.all₂_witnesses (fun state term => witnesses rows state = some term) children
    (fun child member => (witnesses_exact rows child).mpr (inhabited child member))
  exact ⟨terms, (arguments_exact _ _ _).mpr related⟩

/-- Every child in an admitted forest has an admitted term. -/
theorem forest_inhabited (rows : Rows State Symbol) (children : List State) (terms : List (Term Symbol))
    (accepted : All₂ (Admits rows) children terms) : ∀ child ∈ children, ∃ term, Admits rows child term := by
  induction accepted with
  | nil => simp
  | @cons child term children terms first rest ih =>
      intro state member
      rcases List.mem_cons.mp member with same | later
      · subst state
        exact ⟨term, first⟩
      · exact ih state later

/-- Generate the actual child-context extensions for one row in transition and position order. -/
def steps (rows : Rows (Fin count) Symbol) : ConstructorProbeWorklist.Steps (Fin count) (Context Symbol) :=
  fun state => (rows state).flatMap fun (symbol, children) =>
    match arguments (witnesses rows) children with
    | none => []
    | some terms => children.zipIdx.map fun (child, position) =>
        (child, fun outer => Context.frame outer symbol terms position)

/-- Each actual local extension preserves the initial-state context semantics. -/
theorem steps_preserve (rows : Rows (Fin count) Symbol) (root : Fin count) :
    ConstructorProbeWorklist.Preserves (steps rows) (Fits rows root) := by
  intro state context fits entry member
  obtain ⟨row, listed, localMember⟩ := List.mem_flatMap.mp member
  rcases row with ⟨symbol, children⟩
  cases found : arguments (witnesses rows) children with
  | none => simp [found] at localMember
  | some terms =>
      simp only [found] at localMember
      obtain ⟨position, positionMember, same⟩ := List.mem_map.mp localMember
      subst entry
      intro term accepted
      apply fits
      exact .node ⟨symbol, children, fun _ => true⟩ _
        (List.mem_map.mpr ⟨(symbol, children), listed, rfl⟩)
        (forest_replace rows children terms (witness_arguments rows children terms found) position.2 position.1
          ((position_exact children position.1 position.2).mp positionMember) term accepted) rfl

/-- A usable row exposes every one of its child states in the actual context expansion. -/
theorem steps_cover (rows : Rows (Fin count) Symbol) (state child : Fin count)
    (symbol : Symbol) (children : List (Fin count)) (terms : List (Term Symbol))
    (listed : (symbol, children) ∈ rows state) (ready : arguments (witnesses rows) children = some terms)
    (member : child ∈ children) : ∃ extend, (child, extend) ∈ steps rows state := by
  obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
  refine ⟨fun outer => .frame outer symbol terms position, List.mem_flatMap.mpr ?_⟩
  refine ⟨(symbol, children), listed, ?_⟩
  simp only [ready]
  exact List.mem_map.mpr ⟨(child, position), (position_exact children child position).mpr found, rfl⟩

/-- The source begins with the identity context for its initial state. -/
def initial (root : Fin count) : Table (Fin count) (Context Symbol) := put (fun _ => none) root .hole

/-- Run the actual finite FIFO context search after witness convergence. -/
def contexts (rows : Rows (Fin count) Symbol) (root : Fin count) : Table (Fin count) (Context Symbol) :=
  ConstructorProbeWorklist.reach (steps rows) (initial root) [root]

/-- Every stored context is an admitted root context for all admitted hole terms. -/
theorem contexts_sound (rows : Rows (Fin count) Symbol) (root state : Fin count) (context : Context Symbol)
    (stored : contexts rows root state = some context) : Fits rows root state context := by
  apply ConstructorProbeWorklist.reach_property (steps rows) (Fits rows root) (steps_preserve rows root)
    (initial root) [root] ?_ state context stored
  intro key value present
  by_cases same : key = root
  · subst key
    have valueEq : value = .hole := by simpa [initial, put] using present.symm
    subst value
    exact fun _ accepted => accepted
  · simp [initial, put, same] at present

/-- The initial context always survives the worklist. -/
theorem contexts_root (rows : Rows (Fin count) Symbol) (root : Fin count) :
    contexts rows root root = some .hole :=
  ConstructorProbeWorklist.reach_grows (steps rows) (initial root) [root] root .hole (by simp [initial, put])

/-- Every context expansion target has a context when the source queue completes. -/
theorem contexts_closed (rows : Rows (Fin count) Symbol) (root state : Fin count) (context : Context Symbol)
    (stored : contexts rows root state = some context) :
    ∀ entry ∈ steps rows state, ∃ childContext, contexts rows root entry.1 = some childContext := by
  apply ConstructorProbeWorklist.reach_closed (steps rows) (initial root) [root] ?_ state context stored
  intro key value present
  left
  by_cases same : key = root
  · simp [same]
  · simp [initial, put, same] at present

/-- A state occurrence follows actual productive transitions from the root. -/
inductive Occurs (rows : Rows State Symbol) (root : State) : State → Prop where
  | root : Occurs rows root root
  | child : Occurs rows root state → (symbol, children) ∈ rows state →
      All₂ (Admits rows) children terms → child ∈ children → Occurs rows root child

/-- Every state that can occur along a productive root path gets an actual constructed context. -/
theorem contexts_complete (rows : Rows (Fin count) Symbol) (root state : Fin count)
    (occurs : Occurs rows root state) : ∃ context, contexts rows root state = some context := by
  induction occurs with
  | root => exact ⟨.hole, contexts_root rows root⟩
  | @child state symbol children terms child parent listed accepted member ih =>
      obtain ⟨context, stored⟩ := ih
      obtain ⟨arguments, ready⟩ := arguments_available rows children (forest_inhabited rows children terms accepted)
      obtain ⟨extend, entry⟩ := steps_cover rows state child symbol children arguments listed ready member
      exact contexts_closed rows root state context stored (child, extend) entry

/-- The actual finite probe list visits every stored context and every usable transition at its state. -/
def probes (rows : Rows (Fin count) Symbol) (root : Fin count) : List (Symbol × Term Symbol) :=
  (List.finRange count).flatMap fun state =>
    match contexts rows root state with
    | none => []
    | some context => (rows state).filterMap fun (symbol, children) =>
        (arguments (witnesses rows) children).map fun terms => (symbol, plug context (.node symbol terms))

/-- Every emitted codec probe is admitted at the initial state. -/
theorem probes_sound (rows : Rows (Fin count) Symbol) (root : Fin count) (probe : Symbol × Term Symbol)
    (member : probe ∈ probes rows root) : Admits rows root probe.2 := by
  obtain ⟨state, _, localMember⟩ := List.mem_flatMap.mp member
  cases stored : contexts rows root state with
  | none => simp [stored] at localMember
  | some context =>
      simp only [stored] at localMember
      obtain ⟨row, listed, decoded⟩ := List.mem_filterMap.mp localMember
      rcases row with ⟨symbol, children⟩
      cases ready : arguments (witnesses rows) children with
      | none => simp [ready] at decoded
      | some terms =>
          have same : probe = (symbol, plug context (.node symbol terms)) := by simpa [ready] using decoded.symm
          subst probe
          exact contexts_sound rows root state context stored _
            (.node ⟨symbol, children, fun _ => true⟩ terms
              (List.mem_map.mpr ⟨(symbol, children), listed, rfl⟩) (witness_arguments rows children terms ready) rfl)

/-- Every productive transition on a root path contributes its own admitted root probe. -/
theorem probes_cover (rows : Rows (Fin count) Symbol) (root state : Fin count)
    (occurs : Occurs rows root state) (symbol : Symbol) (children : List (Fin count))
    (listed : (symbol, children) ∈ rows state) (terms : List (Term Symbol))
    (accepted : All₂ (Admits rows) children terms) :
    ∃ context arguments, contexts rows root state = some context ∧
      ConstructorProbeWitnesses.arguments (witnesses rows) children = some arguments ∧
      (symbol, plug context (.node symbol arguments)) ∈ probes rows root := by
  obtain ⟨context, stored⟩ := contexts_complete rows root state occurs
  obtain ⟨arguments, ready⟩ := arguments_available rows children (forest_inhabited rows children terms accepted)
  refine ⟨context, arguments, stored, ready, List.mem_flatMap.mpr ?_⟩
  refine ⟨state, List.mem_finRange state, ?_⟩
  simp only [stored]
  exact List.mem_filterMap.mpr ⟨(symbol, children), listed, by simp [ready]⟩

/-- The generated search never takes the model's missing-context fallback. -/
theorem contexts_source_run (rows : Rows (Fin count) Symbol) (root : Fin count) :
    ConstructorProbeWorklist.Runs (steps rows) (initial root) [root] (contexts rows root) := by
  apply ConstructorProbeWorklist.reach_runs
  intro state member
  have same : state = root := by simpa using member
  subst state
  exact ⟨.hole, by simp [initial, put]⟩

/-- A concrete accepting term uses a particular transition at its root or an actual child position. -/
inductive Uses (rows : Rows State Symbol) (owner : State) (label : Symbol) (fields : List State) :
    State → Term Symbol → Prop where
  | here {terms : List (Term Symbol)} : (label, fields) ∈ rows owner → All₂ (Admits rows) fields terms →
      Uses rows owner label fields owner (.node label terms)
  | descend {symbol : Symbol} {children : List State} {state : State} {terms : List (Term Symbol)}
      {position : Nat} {child : State} {term : Term Symbol} :
      (symbol, children) ∈ rows state → All₂ (Admits rows) children terms →
      children[position]? = some child → terms[position]? = some term →
      Uses rows owner label fields child term → Uses rows owner label fields state (.node symbol terms)

/-- A transition used in an actual accepting term is productive and lies on a productive root path. -/
theorem used_transition (rows : Rows State Symbol) (root owner state : State) (label : Symbol) (fields : List State)
    (term : Term Symbol) (used : Uses rows owner label fields state term) (path : Occurs rows root state) :
    Occurs rows root owner ∧ (label, fields) ∈ rows owner ∧ ∃ arguments, All₂ (Admits rows) fields arguments := by
  induction used with
  | here listed accepted => exact ⟨path, listed, _, accepted⟩
  | @descend symbol children state terms position child term listed accepted selected selectedTerm used ih =>
      exact ih (.child path listed accepted (List.mem_iff_getElem?.mpr ⟨position, selected⟩))

/-- Every transition used at any position of an admitted root term has an actual source probe. -/
theorem used_transition_probe (rows : Rows (Fin count) Symbol) (root owner : Fin count)
    (label : Symbol) (fields : List (Fin count)) (term : Term Symbol)
    (used : Uses rows owner label fields root term) :
    ∃ context arguments, contexts rows root owner = some context ∧
      ConstructorProbeWitnesses.arguments (witnesses rows) fields = some arguments ∧
      (label, plug context (.node label arguments)) ∈ probes rows root := by
  obtain ⟨path, listed, terms, accepted⟩ := used_transition rows root owner root label fields term used .root
  exact probes_cover rows root owner path label fields listed terms accepted

/-- The source returns the label of the first selected root term rejected by the codec. -/
def firstRejected (rejects : Term Symbol → Bool) : List (Symbol × Term Symbol) → Option Symbol
  | [] => none
  | (symbol, term) :: rest => if rejects term then some symbol else firstRejected rejects rest

/-- No reported constructor means exactly that every actual selected root probe passed. -/
theorem firstRejected_none (rejects : Term Symbol → Bool) (probes : List (Symbol × Term Symbol)) :
    firstRejected rejects probes = none ↔ ∀ probe ∈ probes, rejects probe.2 = false := by
  induction probes with
  | nil => simp [firstRejected]
  | cons probe rest ih =>
      rcases probe with ⟨symbol, term⟩
      cases rejected : rejects term <;> simp [firstRejected, rejected, ih]

/-- A reported label belongs to a selected root probe that the codec actually rejects. -/
theorem firstRejected_sound (rejects : Term Symbol → Bool) (probes : List (Symbol × Term Symbol))
    (symbol : Symbol) (reported : firstRejected rejects probes = some symbol) :
    ∃ term, (symbol, term) ∈ probes ∧ rejects term = true := by
  induction probes with
  | nil => simp [firstRejected] at reported
  | cons probe rest ih =>
      rcases probe with ⟨label, term⟩
      cases rejected : rejects term with
      | false =>
          obtain ⟨value, member, rejected⟩ := ih (by simpa [firstRejected, rejected] using reported)
          exact ⟨value, List.mem_cons_of_mem _ member, rejected⟩
      | true =>
          have same : label = symbol := by simpa [firstRejected, rejected] using reported
          subst label
          exact ⟨term, by simp, rejected⟩

/-- One rejected selected probe is enough for the actual first-failure search to report a constructor. -/
theorem firstRejected_detects (rejects : Term Symbol → Bool) (probes : List (Symbol × Term Symbol))
    (symbol : Symbol) (term : Term Symbol) (member : (symbol, term) ∈ probes) (rejected : rejects term = true) :
    ∃ reported, firstRejected rejects probes = some reported := by
  cases result : firstRejected rejects probes with
  | some reported => exact ⟨reported, rfl⟩
  | none =>
      have accepted := (firstRejected_none rejects probes).mp result (symbol, term) member
      simp [rejected] at accepted

/-- Execute the actual constructor check on its generated witness/context probes. -/
def undecodable (rows : Rows (Fin count) Symbol) (root : Fin count) (rejects : Term Symbol → Bool) : Option Symbol :=
  firstRejected rejects (probes rows root)

/-- Every reported failure has an actual admitted initial-state term that the codec rejects. -/
theorem undecodable_sound (rows : Rows (Fin count) Symbol) (root : Fin count) (rejects : Term Symbol → Bool)
    (symbol : Symbol) (reported : undecodable rows root rejects = some symbol) :
    ∃ term, (symbol, term) ∈ probes rows root ∧ Admits rows root term ∧ rejects term = true := by
  obtain ⟨term, member, rejected⟩ := firstRejected_sound rejects (probes rows root) symbol reported
  exact ⟨term, member, probes_sound rows root (symbol, term) member, rejected⟩

/-- A local codec failure is stable under every admitted root context and admitted child tuple. -/
def LocallyRejected (rows : Rows State Symbol) (root state : State) (symbol : Symbol) (children : List State)
    (rejects : Term Symbol → Bool) : Prop :=
  ∀ context, Fits rows root state context → ∀ terms, All₂ (Admits rows) children terms →
    rejects (plug context (.node symbol terms)) = true

/-- The source detects a used bad transition under the explicit context-local rejection law. -/
theorem undecodable_detects (rows : Rows (Fin count) Symbol) (root owner : Fin count)
    (label : Symbol) (fields : List (Fin count)) (term : Term Symbol)
    (used : Uses rows owner label fields root term) (rejects : Term Symbol → Bool)
    (bad : LocallyRejected rows root owner label fields rejects) :
    ∃ reported, undecodable rows root rejects = some reported := by
  obtain ⟨context, arguments, stored, ready, member⟩ := used_transition_probe rows root owner label fields term used
  exact firstRejected_detects rejects (probes rows root) label _ member
    (bad context (contexts_sound rows root owner context stored) arguments (witness_arguments rows fields arguments ready))

/-- Passing the actual source probes establishes decoding for those probes only. -/
theorem checkCodec_generated (rows : Rows (Fin count) Symbol) (root : Fin count)
    (decode : Term Symbol → Option Value) :
    Generic.checkCodec decode (probes rows root) = .ok () ↔
      ∀ probe ∈ probes rows root, ∃ value, decode probe.2 = some value :=
  Generic.checkCodec_exact decode (probes rows root)

/-- Every actual discovered context follows productive source transitions from the root. -/
theorem contexts_reachable (rows : Rows (Fin count) Symbol) (root state : Fin count) (context : Context Symbol)
    (stored : contexts rows root state = some context) : Occurs rows root state := by
  apply ConstructorProbeWorklist.reach_property (steps rows) (fun state _ => Occurs rows root state) ?_
    (initial root) [root] ?_ state context stored
  · intro state context path entry member
    obtain ⟨row, listed, localMember⟩ := List.mem_flatMap.mp member
    rcases row with ⟨symbol, children⟩
    cases found : arguments (witnesses rows) children with
    | none => simp [found] at localMember
    | some terms =>
        simp only [found] at localMember
        obtain ⟨position, positionMember, same⟩ := List.mem_map.mp localMember
        subst entry
        exact .child path listed (witness_arguments rows children terms found)
          (List.mem_iff_getElem?.mpr ⟨position.2, (position_exact children position.1 position.2).mp positionMember⟩)
  · intro key value present
    by_cases same : key = root
    · subst key
      exact .root
    · simp [initial, put, same] at present

/-- The computed context map contains exactly the productive root-path states. -/
theorem contexts_exact (rows : Rows (Fin count) Symbol) (root state : Fin count) :
    (∃ context, contexts rows root state = some context) ↔ Occurs rows root state := by
  constructor
  · rintro ⟨context, stored⟩
    exact contexts_reachable rows root state context stored
  · exact contexts_complete rows root state

/-- A constructor label occurs at the root or an actual child of a finite term. -/
inductive Contains (symbol : Symbol) : Term Symbol → Prop where
  | root : Contains symbol (.node symbol terms)
  | child : term ∈ terms → Contains symbol term → Contains symbol (.node label terms)

/-- Generated context application retains every constructor inside its hole term. -/
def KeepsHole (context : Context Symbol) : Prop :=
  ∀ symbol term, Contains symbol term → Contains symbol (plug context term)

/-- Every stored context keeps the supplied hole at its actual valid child positions. -/
theorem contexts_keep_hole (rows : Rows (Fin count) Symbol) (root state : Fin count) (context : Context Symbol)
    (stored : contexts rows root state = some context) : KeepsHole context := by
  apply ConstructorProbeWorklist.reach_property (steps rows) (fun _ context => KeepsHole context) ?_
    (initial root) [root] ?_ state context stored
  · intro state context keeps entry member
    obtain ⟨row, listed, localMember⟩ := List.mem_flatMap.mp member
    rcases row with ⟨label, children⟩
    cases found : arguments (witnesses rows) children with
    | none => simp [found] at localMember
    | some terms =>
        simp only [found] at localMember
        obtain ⟨position, positionMember, same⟩ := List.mem_map.mp localMember
        subst entry
        have bound : position.2 < terms.length := by
          have lengths := (witness_arguments rows children terms found).length_eq
          have index := (List.mem_zipIdx positionMember).2.1
          omega
        intro symbol term present
        apply keeps
        apply Contains.child (term := term)
        · exact List.mem_iff_getElem?.mpr ⟨position.2, by simp [bound]⟩
        · exact present
  · intro key value present
    by_cases same : key = root
    · subst key
      have valueEq : value = .hole := by simpa [initial, put] using present.symm
      subst value
      exact fun _ _ member => member
    · simp [initial, put, same] at present

/-- The tested constructor label really occurs somewhere in its emitted root probe. -/
theorem probes_contain_label (rows : Rows (Fin count) Symbol) (root : Fin count) (probe : Symbol × Term Symbol)
    (member : probe ∈ probes rows root) : Contains probe.1 probe.2 := by
  obtain ⟨state, _, localMember⟩ := List.mem_flatMap.mp member
  cases stored : contexts rows root state with
  | none => simp [stored] at localMember
  | some context =>
      simp only [stored] at localMember
      obtain ⟨row, listed, decoded⟩ := List.mem_filterMap.mp localMember
      rcases row with ⟨symbol, children⟩
      cases ready : arguments (witnesses rows) children with
      | none => simp [ready] at decoded
      | some terms =>
          have same : probe = (symbol, plug context (.node symbol terms)) := by simpa [ready] using decoded.symm
          subst probe
          exact contexts_keep_hole rows root state context stored symbol (.node symbol terms) .root

/-- A reported constructor occurs in a structurally admitted root term that the codec rejects. -/
theorem undecodable_witness (rows : Rows (Fin count) Symbol) (root : Fin count) (rejects : Term Symbol → Bool)
    (symbol : Symbol) (reported : undecodable rows root rejects = some symbol) :
    ∃ term, Admits rows root term ∧ Contains symbol term ∧ rejects term = true := by
  obtain ⟨term, member, admitted, rejected⟩ := undecodable_sound rows root rejects symbol reported
  exact ⟨term, admitted, probes_contain_label rows root (symbol, term) member, rejected⟩

/-- A finite example contains a productive cycle, a repeated child state, and an unproductive cycle. -/
def exampleRows : Rows (Fin 3) Nat := fun state =>
  match state.val with
  | 0 => [(0, [1, 1])]
  | 1 => [(1, [1]), (2, [])]
  | _ => [(3, [2])]

/-- Kernel evaluation checks source witness choice, last-position context choice, and unreachable-cycle exclusion. -/
theorem example_probes :
    witnesses exampleRows 1 = some (.node 2 []) ∧ witnesses exampleRows 2 = none ∧
      contexts exampleRows 0 1 = some (.frame .hole 0 [.node 2 [], .node 2 []] 1) ∧
      probes exampleRows 0 =
        [(0, .node 0 [.node 2 [], .node 2 []]),
         (1, .node 0 [.node 2 [], .node 1 [.node 2 []]]),
         (2, .node 0 [.node 2 [], .node 2 []])] := by
  cbv

end MicroCFTA.ConstructorProbeContexts
