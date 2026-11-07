import MicroCFTA.SourceSizedGroupedRowLanguage
import MicroCFTA.RecursiveUnambiguous

/-!
# Distinct terms in one literal grouped row class

Child classes have distinct terms at their exact node sizes. A weighted
prefix size separates the source product splits. Each nonempty actual group
can then recover its selected value from the reconstructed children.

These facts prove uniqueness for the computed row worker. The proof requires
valid direct-child classes. It does not require a caller-supplied layout or
agreement between the child states of a group. That agreement is needed by
the separate language theorem.
-/

namespace MicroCFTA.SourceSizedGroupedRowUnique

open Language RecursiveSize CompactGroups CompactEdgeRanks
open SourceSizedGroupedChainOrder SourceSizedGroupedRowLanguage

private theorem scaled_unique_sized (inner : Nat → List (Term Symbol))
    (unique : ∀ size, (inner size).Nodup)
    (sized : ∀ size term, term ∈ inner size → nodeSize term = size)
    (factor size : Nat) :
    (scaled factor inner size).Nodup ∧
      ∀ term ∈ scaled factor inner size, factor * nodeSize term = size := by
  by_cases one : factor = 1
  · subst factor
    simpa [scaled] using And.intro (unique size) (sized size)
  · by_cases divisible : size % factor = 0
    · simp only [scaled, ite_eq_right one, ite_eq_left divisible]
      refine ⟨unique (size / factor), ?_⟩
      intro term present
      rw [sized _ term present]
      simpa [divisible] using Nat.div_add_mod size factor
    · simp [scaled, one, divisible]

private theorem groupClass_unique_sized (classAt : State → Nat → List (Term Symbol))
    (unique : ∀ state size, (classAt state size).Nodup)
    (sized : ∀ state size term, term ∈ classAt state size → nodeSize term = size)
    (children : List State) (group : List Nat) (size : Nat) :
    (groupClass classAt children group size).Nodup ∧
      ∀ term ∈ groupClass classAt children group size, group.length * nodeSize term = size := by
  cases group with
  | nil => simp [groupClass]
  | cons first rest =>
      cases read : children[first]? with
      | none => simp [groupClass, read]
      | some state =>
          simpa only [groupClass, read] using
            scaled_unique_sized (classAt state) (unique state) (sized state) _ size

private theorem extendForests_nodup_measure
    (measure : List (Term Symbol) → Nat)
    (prefixes : Nat → List (List (Term Symbol))) (children : Nat → List (Term Symbol))
    (size : Nat)
    (prefixUnique : ∀ part, part ≤ size → (prefixes part).Nodup)
    (prefixSized : ∀ part, part ≤ size → ∀ built ∈ prefixes part, measure built = part)
    (childUnique : ∀ part, part ≤ size → (children part).Nodup) :
    (extendForests prefixes children size).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro part present
    have within : part ≤ size := by have := List.mem_range.mp present; omega
    exact RecursiveUnambiguous.product_nodup _ _
      (prefixUnique part within) (childUnique (size - part) (by omega))
  · apply (List.nodup_range (n := size + 1)).imp_of_mem
    intro first second firstIn secondIn different left leftIn right rightIn same
    obtain ⟨a, aIn, x, _, leftSame⟩ :=
      (by simpa only [List.mem_flatMap, List.mem_map] using leftIn :
        ∃ a ∈ prefixes first, ∃ x ∈ children (size - first), a ++ [x] = left)
    obtain ⟨b, bIn, y, _, rightSame⟩ :=
      (by simpa only [List.mem_flatMap, List.mem_map] using rightIn :
        ∃ b ∈ prefixes second, ∃ y ∈ children (size - second), b ++ [y] = right)
    have prefixesSame := (RecursiveUnambiguous.snoc_unique a b x y
      (leftSame.trans (same.trans rightSame.symm))).1
    have firstSize := prefixSized first (by have := List.mem_range.mp firstIn; omega) a aIn
    have secondSize := prefixSized second (by have := List.mem_range.mp secondIn; omega) b bIn
    exact different (firstSize.symm.trans ((congrArg measure prefixesSame).trans secondSize))

private theorem selectionSize_snoc (selected : List (List Nat × Term Symbol))
    (group : List Nat) (term : Term Symbol) :
    selectionSize (selected ++ [(group, term)]) =
      selectionSize selected + group.length * nodeSize term := by
  simp [selectionSize]

private theorem prefixes_unique
    (generate : List Nat → Nat → List (Term Symbol)) (groups : List (List Nat))
    (groupClasses : ∀ group ∈ groups, ∀ size,
      (generate group size).Nodup ∧
        ∀ term ∈ generate group size, group.length * nodeSize term = size) :
    ∀ size,
      ((groups.foldl (fun built group => extendForests built (generate group)) seed) size).Nodup ∧
      ∀ selected ∈ (groups.foldl
          (fun built group => extendForests built (generate group)) seed) size,
        groups.length = selected.length ∧ selectionSize (groups.zip selected) + 1 = size := by
  induction groups using RecursiveSize.snoc_induction with
  | empty =>
      intro size
      by_cases one : size = 1 <;> simp [seed, one, selectionSize]
  | step groups last ih =>
      have before := ih (fun group present => groupClasses group (List.mem_append_left [last] present))
      have final := groupClasses last (by simp)
      intro size
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨extendForests_nodup_measure
        (fun selected => selectionSize (groups.zip selected) + 1) _ _ size
        (fun part _ => (before part).1)
        (fun part _ selected present => ((before part).2 selected present).2)
        (fun part _ => (final part).1), ?_⟩
      intro selected present
      obtain ⟨part, partIn, earlier, earlierIn, term, termIn, same⟩ :=
        (by simpa only [extendForests, List.mem_flatMap, List.mem_map] using present :
          ∃ part ∈ List.range (size + 1), ∃ earlier,
            earlier ∈ (groups.foldl
              (fun built group => extendForests built (generate group)) seed) part ∧
            ∃ term, term ∈ generate last (size - part) ∧ earlier ++ [term] = selected)
      have previousFacts := (before part).2 earlier earlierIn
      have finalSize := (final (size - part)).2 term termIn
      have within := List.mem_range.mp partIn
      subst selected
      refine ⟨by simp [previousFacts.1], ?_⟩
      rw [List.zip_append previousFacts.1]
      simp only [List.zip_cons_cons, List.zip_nil_left]
      rw [selectionSize_snoc]
      omega

private theorem all₂_of_zip {A B : Type} (relation : A → B → Prop)
    (left : List A) (right : List B) (length : left.length = right.length)
    (each : ∀ pair ∈ left.zip right, relation pair.1 pair.2) : All₂ relation left right := by
  induction left generalizing right with
  | nil =>
      have empty : right = [] := List.length_eq_zero_iff.mp length.symm
      subst right
      exact .nil
  | cons first rest ih =>
      cases right with
      | nil => simp at length
      | cons value values =>
          exact .cons (each (first, value) (by simp))
            (ih values (by simpa using length)
              (fun pair present => each pair (List.mem_cons_of_mem (first, value) present)))

private theorem selections_unique (groups : List (List Nat))
    (nonempty : ∀ group ∈ groups, group ≠ []) (values : List (Term Symbol))
    (first second : List (Term Symbol))
    (firstAgree : All₂ (fun group term => ∀ index ∈ group, values[index]? = some term) groups first)
    (secondAgree : All₂ (fun group term => ∀ index ∈ group, values[index]? = some term) groups second) :
    first = second := by
  induction groups generalizing first second with
  | nil => cases firstAgree; cases secondAgree; rfl
  | cons group groups ih =>
      cases firstAgree with
      | @cons _ first _ firsts firstRead firstRest =>
          cases secondAgree with
          | @cons _ second _ seconds secondRead secondRest =>
              obtain ⟨index, indexIn⟩ := List.exists_mem_of_ne_nil group (nonempty group (by simp))
              have same := Option.some.inj ((firstRead index indexIn).symm.trans (secondRead index indexIn))
              subst second
              exact congrArg (List.cons first)
                (ih (fun item present => nonempty item (List.mem_cons_of_mem group present))
                  firsts seconds firstRest secondRest)

/-- Every actual nonempty group recovers its chosen term from the assembled node. -/
theorem assemble_injective (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (first second : List (Term Symbol))
    (firstLength : (childGroups arity classes).length = first.length)
    (secondLength : (childGroups arity classes).length = second.length)
    (same : assemble symbol arity (childGroups arity classes) first =
      assemble symbol arity (childGroups arity classes) second) : first = second := by
  let groups := childGroups arity classes
  have firstLayout : (groups.zip first).map Prod.fst = groups :=
    List.map_fst_zip (Nat.le_of_eq firstLength)
  have secondLayout : (groups.zip second).map Prod.fst = groups :=
    List.map_fst_zip (Nat.le_of_eq secondLength)
  have firstRead := generated_agreement symbol arity classes (groups.zip first) firstLayout
  have secondRead := generated_agreement symbol arity classes (groups.zip second) secondLayout
  have childrenSame := (Term.node.inj same).2
  apply selections_unique groups (childGroups_nonempty arity classes valid)
    (childrenOf symbol arity (groups.zip first)) first second
  · exact all₂_of_zip _ groups first firstLength
      (fun pair present => firstRead pair present)
  · apply all₂_of_zip _ groups second secondLength
    intro pair present index indexIn
    rw [childrenSame]
    exact secondRead pair present index indexIn

/-- Distinct exact-size child classes give a distinct literal grouped row class.
Child-state sharing is not needed for this uniqueness law. -/
theorem rowClass_nodup (classAt : State → Nat → List (Term Symbol))
    (childSized : ∀ state size term, term ∈ classAt state size → nodeSize term = size)
    (childUnique : ∀ state size, (classAt state size).Nodup)
    (symbol : Symbol) (children : List State) (classes : List (List Nat))
    (valid : ValidClasses children.length classes) (size : Nat) :
    (rowClass classAt symbol children classes size).Nodup := by
  let groups := childGroups children.length classes
  have prefixes := prefixes_unique (groupClass classAt children) groups
    (fun group _ => groupClass_unique_sized classAt childUnique childSized children group)
  apply List.pairwise_map.mpr
  apply (prefixes size).1.imp_of_mem
  intro first second firstIn secondIn different same
  exact different (assemble_injective symbol children.length classes valid first second
    ((prefixes size).2 first firstIn).1 ((prefixes size).2 second secondIn).1 same)

end MicroCFTA.SourceSizedGroupedRowUnique
