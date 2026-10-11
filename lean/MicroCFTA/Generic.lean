import MicroCFTA.Construction
import MicroCFTA.DistinctRank

/-!
# Finite datatype grammar discovery

This model follows `deriveFTAWithGrowthLimit`: reuse a visited type before
checking growth, check an atomic domain, allocate its row, then visit its fields
from left to right. A finite list bounds the descriptor states under review.
The driver terminates by the number of unvisited states and pending tasks.
The list is a finite input representation, not an enumeration of datatype values.
-/

namespace MicroCFTA.Generic

open Language

/-- One constructor and the fully applied types of its ordered fields. -/
abbrev Row (State Symbol : Type) := List (Symbol × List State)

/-- Atomic fields require a finite domain; algebraic fields give constructor rows. -/
inductive Description (State Symbol : Type) where
  | atomic
  | algebraic (constructors : Row State Symbol)

/-- Source construction failures retain the type or constructor that failed. -/
inductive Error (State Symbol : Type) where
  | missingDomain (state : State)
  | nonAtomicDomain (state : State)
  | nonRegularRecursion (limit : Int) (first next : State)
  | unknownConstructors (names : List Symbol)
  deriving DecidableEq, Repr

/-- Read one type's row after applying its explicit atomic-domain policy. -/
def readRow (describe : State → Description State Symbol)
    (domains : State → Option (List Symbol)) (state : State) : Except (Error State Symbol) (Row State Symbol) :=
  match describe state, domains state with
  | .atomic, none => .error (.missingDomain state)
  | .atomic, some literals => .ok (literals.map fun symbol => (symbol, []))
  | .algebraic _, some _ => .error (.nonAtomicDomain state)
  | .algebraic row, none => .ok row

/-- Missing domains are construction failures, while an empty explicit domain is valid. -/
theorem empty_domain_is_not_missing (state : State) :
    readRow (Symbol := Symbol) (fun _ => .atomic) (fun _ => none) state =
      .error (.missingDomain state) ∧
    readRow (Symbol := Symbol) (fun _ => .atomic) (fun _ => some []) state = .ok [] := by
  exact ⟨rfl, rfl⟩

/-- Increasing applications of one type constructor along the current ancestor path. -/
def growthPairs [DecidableEq Kind] (kind : State → Kind) (typeSize : State → Nat)
    (state : State) (ancestors : List State) : List (State × State) :=
  let chain := (ancestors.filter (fun ancestor => decide (kind ancestor = kind state))).reverse ++ [state]
  (chain.zip chain.tail).filter (fun pair => decide (typeSize pair.1 < typeSize pair.2))

/-- The source reports the first increasing pair when the growth limit is exceeded. -/
def growthError [DecidableEq Kind] (kind : State → Kind) (typeSize : State → Nat)
    (limit : Int) (state : State) (ancestors : List State) : Option (Error State Symbol) :=
  let pairs := growthPairs kind typeSize state ancestors
  if (pairs.length : Int) > limit then
    pairs.head?.map (fun pair => .nonRegularRecursion limit pair.1 pair.2)
  else none

/-- A pending type remembers the nearest-first ancestor chain of its discovery. -/
abbrev Task (State : Type) := State × List State

/-- All constructor fields of one type, in source traversal order. -/
def children (row : Row State Symbol) : List State := row.flatMap Prod.snd

/-- Visit unallocated types depth first, retaining every successful row exactly once. -/
def discover [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (checkGrowth : State → List State → Option (Error State Symbol))
    (available : List State) (pending : List (Task State)) :
    Except (Error State Symbol) (List (State × Row State Symbol)) :=
  match pending with
  | [] => .ok []
  | (state, ancestors) :: rest =>
      if _fresh : state ∈ available then
        match checkGrowth state ancestors with
        | some error => .error error
        | none =>
            match rowOf state with
            | .error error => .error error
            | .ok row =>
                match discover rowOf checkGrowth (available.erase state)
                    ((children row).map (fun child => (child, state :: ancestors)) ++ rest) with
                | .error error => .error error
                | .ok rows => .ok ((state, row) :: rows)
      else discover rowOf checkGrowth available rest
termination_by (available.length, pending.length)
decreasing_by
  · apply Prod.Lex.left
    rw [List.length_erase_of_mem _fresh]
    have positive := List.length_pos_of_mem _fresh
    omega
  · apply Prod.Lex.right
    simp

/-- Newly allocated states in a discovery result. -/
def states (rows : List (State × Row State Symbol)) : List State := rows.map Prod.fst

/-- A requested state was already allocated, or occurs in the new result. -/
def Covered (available : List State) (rows : List (State × Row State Symbol)) (state : State) : Prop :=
  state ∉ available ∨ state ∈ states rows

/-- Adding a newly allocated row covers every state covered after its removal. -/
theorem covered_cons [DecidableEq State] (available : List State) (rows : List (State × Row State Symbol))
    (state target : State) (row : Row State Symbol)
    (covered : Covered (available.erase state) rows target) :
    Covered available ((state, row) :: rows) target := by
  by_cases same : target = state
  · exact Or.inr (by simp [states, same])
  · rcases covered with absent | present
    · exact Or.inl (fun member => absent ((List.mem_erase_of_ne same).mpr member))
    · exact Or.inr (by simpa [states] using Or.inr present)

/-- Discovery allocates exact rows once and covers every pending type and child. -/
structure DiscoverySpec
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (available : List State) (pending : List (Task State))
    (rows : List (State × Row State Symbol)) : Prop where
  allocated : ∀ entry, entry ∈ rows → entry.1 ∈ available
  exactRows : ∀ entry, entry ∈ rows → rowOf entry.1 = .ok entry.2
  distinct : (states rows).Nodup
  requested : ∀ task, task ∈ pending → Covered available rows task.1
  closed : ∀ entry, entry ∈ rows → ∀ child, child ∈ children entry.2 → Covered available rows child

/-- Finite worklist discovery cannot omit a requested type or a constructor field. -/
theorem discover_correct [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (checkGrowth : State → List State → Option (Error State Symbol))
    (available : List State) (pending : List (Task State))
    (rows : List (State × Row State Symbol)) (unique : available.Nodup)
    (successful : discover rowOf checkGrowth available pending = .ok rows) :
    DiscoverySpec rowOf available pending rows := by
  induction available, pending using discover.induct rowOf checkGrowth generalizing rows with
  | case1 available =>
      have empty : rows = [] := by simpa [discover] using successful.symm
      subst rows
      exact ⟨by simp, by simp, List.nodup_nil, by simp, by simp⟩
  | case2 available state ancestors rest fresh error rejected =>
      simp [discover, fresh, rejected] at successful
  | case3 available state ancestors rest fresh allowed error rejected =>
      simp [discover, fresh, allowed, rejected] at successful
  | case4 available state ancestors rest fresh allowed row rowCorrect error rejected ih =>
      simp [discover, fresh, allowed, rowCorrect, rejected] at successful
  | case5 available state ancestors rest fresh allowed row rowCorrect found tail ih =>
      have same : (state, row) :: found = rows := by
        simpa [discover, fresh, allowed, rowCorrect, tail] using successful
      subst rows
      have facts := ih found (List.Pairwise.erase state unique) tail
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro entry present
        rcases List.mem_cons.mp present with rfl | member
        · exact fresh
        · exact List.mem_of_mem_erase (facts.allocated entry member)
      · intro entry present
        rcases List.mem_cons.mp present with rfl | member
        · exact rowCorrect
        · exact facts.exactRows entry member
      · apply List.nodup_cons.mpr
        refine ⟨?_, facts.distinct⟩
        intro present
        obtain ⟨entry, member, same⟩ := List.mem_map.mp present
        have allocated := facts.allocated entry member
        rw [same] at allocated
        exact unique.not_mem_erase allocated
      · intro task present
        rcases List.mem_cons.mp present with rfl | member
        · exact Or.inr (by simp [states])
        · exact covered_cons available found state task.1 row
            (facts.requested task (List.mem_append_right _ member))
      · intro entry present child childMember
        apply covered_cons available found state child row
        rcases List.mem_cons.mp present with rfl | member
        · exact facts.requested (child, state :: ancestors)
            (List.mem_append_left _ (List.mem_map.mpr ⟨child, childMember, rfl⟩))
        · exact facts.closed entry member child childMember
  | case6 available state ancestors rest old ih =>
      have tail : discover rowOf checkGrowth available rest = .ok rows := by
        simpa [discover, old] using successful
      have facts := ih rows unique tail
      refine ⟨facts.allocated, facts.exactRows, facts.distinct, ?_, facts.closed⟩
      intro task present
      rcases List.mem_cons.mp present with rfl | member
      · exact Or.inl old
      · exact facts.requested task member

/-- Convert constructor descriptors to ordinary tree-automaton transitions. -/
def edges (row : Row State Symbol) : List (Edge State Symbol) :=
  row.map fun (symbol, fields) => ⟨symbol, fields, fun _ => true⟩

/-- The semantic descriptor graph. Failed rows are meaningful only as construction errors. -/
def declaredAutomaton (rowOf : State → Except (Error State Symbol) (Row State Symbol)) :
    Automaton State Symbol :=
  fun state => match rowOf state with
    | .error _ => []
    | .ok row => edges row

/-- Read the actual rows retained by successful discovery. -/
def discoveredAutomaton [DecidableEq State] (rows : List (State × Row State Symbol)) :
    Automaton State Symbol :=
  fun state => rows.flatMap fun entry => if entry.1 = state then edges entry.2 else []

/-- Each discovered edge is an unchanged declared edge. -/
theorem discovered_edge_sound [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (rows : List (State × Row State Symbol))
    (exactRows : ∀ entry, entry ∈ rows → rowOf entry.1 = .ok entry.2)
    (state : State) (edge : Edge State Symbol) (present : edge ∈ discoveredAutomaton rows state) :
    edge ∈ declaredAutomaton rowOf state := by
  obtain ⟨entry, member, edgeMember⟩ := List.mem_flatMap.mp present
  by_cases same : entry.1 = state
  · have declared := exactRows entry member
    subst state
    simpa [declaredAutomaton, declared] using edgeMember
  · simp [same] at edgeMember

/-- Every declared edge of an allocated state is retained. -/
theorem discovered_edge_complete [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (rows : List (State × Row State Symbol))
    (exactRows : ∀ entry, entry ∈ rows → rowOf entry.1 = .ok entry.2)
    (state : State) (allocated : state ∈ states rows) (edge : Edge State Symbol)
    (present : edge ∈ declaredAutomaton rowOf state) : edge ∈ discoveredAutomaton rows state := by
  obtain ⟨entry, member, same⟩ := List.mem_map.mp allocated
  have declared := exactRows entry member
  subst state
  exact List.mem_flatMap.mpr ⟨entry, member, by
    simpa [declaredAutomaton, declared] using present⟩

/-- Discovery over a complete finite descriptor set closes every retained child state. -/
theorem discovered_closed [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (available : List State) (pending : List (Task State))
    (rows : List (State × Row State Symbol))
    (complete : ∀ state, state ∈ available) (spec : DiscoverySpec rowOf available pending rows)
    (state : State) (edge : Edge State Symbol) (present : edge ∈ discoveredAutomaton rows state)
    (child : State) (childMember : child ∈ edge.children) : child ∈ states rows := by
  obtain ⟨entry, member, edgeMember⟩ := List.mem_flatMap.mp present
  by_cases same : entry.1 = state
  · simp only [same, ite_true] at edgeMember
    obtain ⟨constructor, constructorMember, edgeEq⟩ := List.mem_map.mp edgeMember
    subst edge
    have field : child ∈ children entry.2 :=
      List.mem_flatMap.mpr ⟨constructor, constructorMember, childMember⟩
    exact (spec.closed entry member child field).resolve_left (fun absent => absent (complete child))
  · simp [same] at edgeMember

/-- Retaining exact rows cannot introduce a new accepted term. -/
theorem discovered_sound [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (rows : List (State × Row State Symbol))
    (exactRows : ∀ entry, entry ∈ rows → rowOf entry.1 = .ok entry.2)
    {state : State} {term : Term Symbol} (accepted : Accepts (discoveredAutomaton rows) state term) :
    Accepts (declaredAutomaton rowOf) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (Accepts (declaredAutomaton rowOf)) states terms) with
  | node edge terms present children guard ih =>
      exact .node edge terms (discovered_edge_sound rowOf rows exactRows _ _ present) ih guard
  | nil => exact .nil
  | cons first rest firstProof restProof => exact .cons firstProof restProof

/-- Exact closed rows retain every finite term derivable from an allocated type. -/
theorem discovered_complete [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (rows : List (State × Row State Symbol))
    (exactRows : ∀ entry, entry ∈ rows → rowOf entry.1 = .ok entry.2)
    (closed : ∀ state edge, edge ∈ discoveredAutomaton rows state →
      ∀ child, child ∈ edge.children → child ∈ states rows)
    {state : State} {term : Term Symbol} (accepted : Accepts (declaredAutomaton rowOf) state term) :
    state ∈ states rows → Accepts (discoveredAutomaton rows) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun qs terms _ => (∀ q, q ∈ qs → q ∈ states rows) →
      All₂ (Accepts (discoveredAutomaton rows)) qs terms) with
  | @node state edge terms present children guard ih =>
      intro allocated
      have retained := discovered_edge_complete rowOf rows exactRows state allocated edge present
      exact .node edge terms retained (ih (closed state edge retained)) guard
  | nil allocated => exact .nil
  | @cons first term rest terms accepted children firstProof restProof allocated =>
      exact .cons (firstProof (allocated first (by simp)))
        (restProof (fun child present => allocated child (by simp [present])))

/-- Successful finite descriptor discovery preserves the entire root language. -/
theorem discovery_acceptance [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (checkGrowth : State → List State → Option (Error State Symbol))
    (available : List State) (unique : available.Nodup) (complete : ∀ state, state ∈ available)
    (root : State) (rows : List (State × Row State Symbol))
    (successful : discover rowOf checkGrowth available [(root, [])] = .ok rows)
    (term : Term Symbol) :
    Accepts (discoveredAutomaton rows) root term ↔ Accepts (declaredAutomaton rowOf) root term := by
  have spec := discover_correct rowOf checkGrowth available [(root, [])] rows unique successful
  have rootPresent : root ∈ states rows :=
    (spec.requested (root, []) (by simp)).resolve_left (fun absent => absent (complete root))
  exact ⟨discovered_sound rowOf rows spec.exactRows,
    fun accepted => discovered_complete rowOf rows spec.exactRows
      (discovered_closed rowOf available [(root, [])] rows complete spec) accepted rootPresent⟩

/-- Run the source domain and growth checks in the finite discovery driver. -/
def derive [DecidableEq State] [DecidableEq Kind]
    (describe : State → Description State Symbol) (domains : State → Option (List Symbol))
    (kind : State → Kind) (typeSize : State → Nat) (limit : Int)
    (allStates : List State) (root : State) : Except (Error State Symbol) (List (State × Row State Symbol)) :=
  discover (readRow describe domains) (growthError kind typeSize limit) allStates [(root, [])]

/-- The source reuse check occurs before a new growth check. -/
theorem previously_allocated_skips_growth [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (checkGrowth : State → List State → Option (Error State Symbol))
    (available : List State) (state : State) (ancestors : List State) (rest : List (Task State))
    (visited : state ∉ available) :
    discover rowOf checkGrowth available ((state, ancestors) :: rest) =
      discover rowOf checkGrowth available rest := by
  rw [discover]
  simp [visited]

/-- A missing domain propagates as its source error when that type is first visited. -/
theorem missing_domain_error [DecidableEq State]
    (describe : State → Description State Symbol) (domains : State → Option (List Symbol))
    (checkGrowth : State → List State → Option (Error State Symbol))
    (available : List State) (state : State) (ancestors : List State) (rest : List (Task State))
    (fresh : state ∈ available) (allowed : checkGrowth state ancestors = none)
    (atomic : describe state = .atomic) (missing : domains state = none) :
    discover (readRow describe domains) checkGrowth available ((state, ancestors) :: rest) =
      .error (.missingDomain state) := by
  rw [discover]
  simp [fresh, allowed, readRow, atomic, missing]

/-- A source growth rejection propagates without returning a partial grammar. -/
theorem growth_error [DecidableEq State]
    (rowOf : State → Except (Error State Symbol) (Row State Symbol))
    (checkGrowth : State → List State → Option (Error State Symbol))
    (available : List State) (state : State) (ancestors : List State) (rest : List (Task State))
    (fresh : state ∈ available) (error : Error State Symbol)
    (rejected : checkGrowth state ancestors = some error) :
    discover rowOf checkGrowth available ((state, ancestors) :: rest) = .error error := by
  rw [discover]
  simp [fresh, rejected]

/-- A zero growth limit rejects the first increasing same-constructor type. -/
theorem growth_limit_example :
    growthError (Symbol := Nat) (fun _ : Nat => ()) id 0 1 [0] =
      some (.nonRegularRecursion 0 0 1) := by decide +kernel

/-- Constructor names unknown to the grammar, with duplicates removed. -/
def unknownNames [DecidableEq Symbol] (known requested : List Symbol) : List Symbol :=
  (requested.filter (fun name => decide (name ∉ known))).eraseDups

/-- A constructor annotation fails exactly when it names an absent constructor. -/
theorem unknownNames_exact [DecidableEq Symbol] (known requested : List Symbol) (name : Symbol) :
    name ∈ unknownNames known requested ↔ name ∈ requested ∧ name ∉ known := by
  simp [unknownNames]

/-- Annotation validation preserves unknown-constructor failures. -/
def checkAnnotations [DecidableEq Symbol] (known requested : List Symbol) :
    Except (Error State Symbol) Unit :=
  let unknown := unknownNames known requested
  if unknown = [] then .ok () else .error (.unknownConstructors unknown)

/-- Successful annotation lookup cannot silently use a default for a misspelled name. -/
theorem checkAnnotations_exact [DecidableEq Symbol] (known requested : List Symbol) :
    checkAnnotations (State := State) known requested = .ok () ↔
      ∀ name, name ∈ requested → name ∈ known := by
  unfold checkAnnotations
  by_cases empty : unknownNames known requested = []
  · simp only [empty, ite_true, true_iff]
    intro name present
    by_cases found : name ∈ known
    · exact found
    · have bad := (unknownNames_exact known requested name).mpr ⟨present, found⟩
      simp [empty] at bad
  · simp only [empty, ite_false, reduceCtorEq, false_iff]
    intro allKnown
    have noMembers : ∀ name, name ∉ unknownNames known requested := by
      intro name present
      have bad := (unknownNames_exact known requested name).mp present
      exact bad.2 (allKnown name bad.1)
    exact empty (List.eq_nil_iff_forall_not_mem.mpr noMembers)

/-- The datatype codec contract on admitted constructor terms. -/
structure Codec (Accepted : Term Symbol → Prop) (Value : Type) where
  decode : Term Symbol → Option Value
  encode : Value → Term Symbol
  total : ∀ term, Accepted term → ∃ value, decode term = some value
  encodeAfterDecode : ∀ term value, Accepted term → decode term = some value → encode value = term

/-- Every admitted term rank has a decoded datatype value under the codec contract. -/
theorem codec_rank_total (index : DistinctRank.Index Accepted) (codec : Codec Accepted Value)
    (rank : Fin index.count) : ∃ value, codec.decode (index.decode rank).val = some value :=
  codec.total _ (index.decode rank).property

/-- Codec round trips make value decoding injective on distinct accepted term ranks. -/
theorem codec_rank_injective (index : DistinctRank.Index Accepted) (codec : Codec Accepted Value)
    (first second : Fin index.count) (value : Value)
    (decodedFirst : codec.decode (index.decode first).val = some value)
    (decodedSecond : codec.decode (index.decode second).val = some value) : first = second := by
  have firstTerm := codec.encodeAfterDecode _ value (index.decode first).property decodedFirst
  have secondTerm := codec.encodeAfterDecode _ value (index.decode second).property decodedSecond
  exact index.decode_injective first second (Subtype.ext (firstTerm.symm.trans secondTerm))

/-- A failed constructor probe retains its constructor label. -/
inductive CodecError (Symbol : Type) where
  | undecodableConstructor (symbol : Symbol)
  deriving DecidableEq, Repr

/-- Check one selected term for each constructor before using its datatype codec. -/
def checkCodec (decode : Term Symbol → Option Value) : List (Symbol × Term Symbol) →
    Except (CodecError Symbol) Unit
  | [] => .ok ()
  | (symbol, term) :: rest =>
      match decode term with
      | none => .error (.undecodableConstructor symbol)
      | some _ => checkCodec decode rest

/-- Successful constructor probes establish decoding only for the actual probe terms. -/
theorem checkCodec_exact (decode : Term Symbol → Option Value) (probes : List (Symbol × Term Symbol)) :
    checkCodec decode probes = .ok () ↔
      ∀ probe, probe ∈ probes → ∃ value, decode probe.2 = some value := by
  induction probes with
  | nil => simp [checkCodec]
  | cons probe rest ih =>
      rcases probe with ⟨symbol, term⟩
      cases decoded : decode term with
      | none => simp [checkCodec, decoded]
      | some value => simp [checkCodec, decoded, ih]

/-- A constructor probe does not establish totality on other terms of that constructor. -/
theorem finite_probes_do_not_prove_codec_totality :
    let decode : Term Nat → Option Nat := fun term =>
      if term.height = 2 then some 0 else none
    checkCodec decode [(0, .node 0 [.node 1 []])] = .ok () ∧
      decode (.node 0 [.node 2 [.node 1 []]]) = none := by simp [checkCodec, Term.height]

end MicroCFTA.Generic
