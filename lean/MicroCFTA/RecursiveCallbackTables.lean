import MicroCFTA.RecursiveCallbackTermination

/-!
# Ordered tables for source recursive callbacks

Finite leaf tables only expose their already finite class selectors. The
body table uses the source class order and mixed-radix products. These
tables state correspondence; the inverse callback does not enumerate them.
-/
namespace MicroCFTA.RecursiveCallbackTables
open Language GeneratorCombinators IntegerTermViews SizedRank RecursiveCallbackTermination

/-- A finite leaf selector is total exactly on its declared class interval. -/
def FiniteIndex (source : Finite Symbol) : Prop :=
  ∀ position, (∃ term, source.select position = some term) ↔ position.rank < source.counts position.size

/-- Tabulate only the finite class interval; valid selectors never use the default. -/
def finiteClass (source : Finite Symbol) (size : Nat) : List (EngineTerm Symbol) :=
  List.ofFn fun rank : Fin (source.counts size) =>
    (source.select ⟨size, rank.val⟩).getD (.node .pure [])

theorem finite_length (source : Finite Symbol) (size : Nat) :
    (finiteClass source size).length = source.counts size := by simp [finiteClass]

/-- Finite tabulation retains the leaf's actual selected rank and rejects invalid ranks. -/
theorem finite_lookup (source : Finite Symbol) (valid : FiniteIndex source) (position : Position)
    (term : EngineTerm Symbol) :
    (finiteClass source position.size)[position.rank]? = some term ↔ source.select position = some term := by
  by_cases within : position.rank < source.counts position.size
  · obtain ⟨selected, found⟩ := (valid position).mpr within
    cases position with
    | mk size rank => simp [finiteClass, within, found]
  · have absent : source.select position = none := by
      cases found : source.select position with
      | none => rfl
      | some term => exact False.elim (within ((valid position).mp ⟨term, found⟩))
    simp [finiteClass, within, absent]

/-- Every finite leaf has its own count/selector correspondence. -/
def LeavesIndexed : Recipe Symbol → Prop
  | .finite source => FiniteIndex source
  | .occurrence => True
  | .map inner | .pay inner | .label _ inner => LeavesIndexed inner
  | .choice left right | .ap left right => LeavesIndexed left ∧ LeavesIndexed right

/-- Read source body classes in their complete ordered member sequence. -/
def classTerms (environment : Nat → List (EngineTerm Symbol)) : Recipe Symbol → Nat → List (EngineTerm Symbol)
  | .finite source, size => finiteClass source size
  | .occurrence, size => environment size
  | .map inner, size => classTerms environment inner size
  | .pay inner, size => match size with | 0 => [] | size + 1 => classTerms environment inner size
  | .choice left right, size =>
      (classTerms environment left size).map (fun term => .node (.choice 0) [term]) ++
      (classTerms environment right size).map (fun term => .node (.choice 1) [term])
  | .ap functions arguments, size =>
      (List.range (size + 1)).flatMap fun split => Decoder.applyValues
        ((classTerms environment functions split).map (fun f x => .node .apply [f, x]))
        (classTerms environment arguments (size - split))
  | .label symbol inner, size => match size with
      | 0 => []
      | size + 1 => (classTerms environment inner size).map (SupportTerms.labelTerm symbol)

/-- The table length is the actual source count recurrence. -/
theorem class_length (environment : Nat → List (EngineTerm Symbol)) (self : Nat → Nat)
    (rootCounts : ∀ size, (environment size).length = self size) (recipe : Recipe Symbol) (size : Nat) :
    (classTerms environment recipe size).length = counts self recipe size := by
  induction recipe generalizing size with
  | finite source => exact finite_length source size
  | occurrence => exact rootCounts size
  | map inner ih => exact ih size
  | pay inner ih | label symbol inner ih => cases size <;> simp [classTerms, counts, ih]
  | choice left right ihl ihr => simp [classTerms, counts, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [classTerms, counts, List.length_flatMap, Decoder.length_applyValues, ihf, iha]

/-- Every successful table lookup has a valid source class rank. -/
theorem lookup_bound (environment : Nat → List (EngineTerm Symbol)) (self : Nat → Nat)
    (rootCounts : ∀ size, (environment size).length = self size) (recipe : Recipe Symbol)
    (position : Position) (term : EngineTerm Symbol)
    (found : (classTerms environment recipe position.size)[position.rank]? = some term) :
    position.rank < counts self recipe position.size := by
  rw [← class_length environment self rootCounts recipe position.size]
  exact (List.getElem?_eq_some_iff.mp found).1

/-- Source product positions replay the selected child terms in the complete class table. -/
theorem product_replay (environment : Nat → List (EngineTerm Symbol)) (self : Nat → Nat)
    (rootCounts : ∀ size, (environment size).length = self size) (functions arguments : Recipe Symbol)
    (first second : Position) (function argument : EngineTerm Symbol)
    (firstFound : (classTerms environment functions first.size)[first.rank]? = some function)
    (secondFound : (classTerms environment arguments second.size)[second.rank]? = some argument) :
    let position := productPosition (counts self functions) (counts self arguments) first second
    (classTerms environment (.ap functions arguments) position.size)[position.rank]? =
      some (.node .apply [function, argument]) := by
  have replay := productPosition_replay
    (fun size => (classTerms environment functions size).map (fun f x => Term.node Label.apply [f, x]))
    (classTerms environment arguments) first second
    (by simpa using (List.getElem?_eq_some_iff.mp firstFound).1)
    (List.getElem?_eq_some_iff.mp secondFound).1
  simp only [List.length_map, class_length environment self rootCounts] at replay
  simpa only [productPosition, classTerms, List.getElem?_map, firstFound, secondFound,
    Option.map_some, Option.bind_some] using replay

/-- A valid product class rank has a valid source size split and two component ranks. -/
theorem product_split (left right : Nat → Nat) (position : Position)
    (within : position.rank < ((List.range (position.size + 1)).map fun split => left split * right (position.size - split)).sum) :
    ∃ first second, productPosition left right first second = position ∧
      first.rank < left first.size ∧ second.rank < right second.size := by
  obtain ⟨split, found⟩ := (sizeClassOf_exists_iff (splitCounts left right position.size) position.rank).mpr
    (by simpa [splitCounts, List.map_map, Function.comp_def] using within)
  obtain ⟨count, member, bounded⟩ := sizeClassOf_valid _ _ split found
  obtain ⟨size, _, same⟩ := List.mem_map.mp member
  have sameSize : size = split.size := congrArg Prod.fst same
  have sameCount : left size * right (position.size - size) = count := congrArg Prod.snd same
  have bound : split.rank < left split.size * right (position.size - split.size) := by
    rw [← sameSize, sameCount]
    exact bounded
  have components := Probability.split_lt bound
  exact ⟨⟨split.size, (Probability.splitRank (right (position.size - split.size)) split.rank).1⟩,
    ⟨position.size - split.size, (Probability.splitRank (right (position.size - split.size)) split.rank).2⟩,
    productPosition_selectedSplit left right position split found, components.1, components.2⟩

/-- A product table lookup comes from the source's two exact child positions. -/
theorem product_lookup (environment : Nat → List (EngineTerm Symbol)) (self : Nat → Nat)
    (rootCounts : ∀ size, (environment size).length = self size) (functions arguments : Recipe Symbol)
    (position : Position) (term : EngineTerm Symbol)
    (found : (classTerms environment (.ap functions arguments) position.size)[position.rank]? = some term) :
    ∃ first second function argument,
      productPosition (counts self functions) (counts self arguments) first second = position ∧
      (classTerms environment functions first.size)[first.rank]? = some function ∧
      (classTerms environment arguments second.size)[second.rank]? = some argument ∧
      term = .node .apply [function, argument] := by
  have within := lookup_bound environment self rootCounts (.ap functions arguments) position term found
  obtain ⟨first, second, same, firstValid, secondValid⟩ := product_split _ _ position within
  have firstWithin : first.rank < (classTerms environment functions first.size).length := by
    simpa [class_length environment self rootCounts] using firstValid
  have secondWithin : second.rank < (classTerms environment arguments second.size).length := by
    simpa [class_length environment self rootCounts] using secondValid
  let function := (classTerms environment functions first.size)[first.rank]
  let argument := (classTerms environment arguments second.size)[second.rank]
  have firstFound : (classTerms environment functions first.size)[first.rank]? = some function :=
    List.getElem?_eq_getElem firstWithin
  have secondFound : (classTerms environment arguments second.size)[second.rank]? = some argument :=
    List.getElem?_eq_getElem secondWithin
  have replay := product_replay environment self rootCounts functions arguments first second function argument firstFound secondFound
  rw [same] at replay
  exact ⟨first, second, function, argument, same, firstFound, secondFound, Option.some.inj (found.symm.trans replay)⟩

end MicroCFTA.RecursiveCallbackTables
