import MicroCFTA.Language

/-!
# Token-prefix exclusion and deterministic child boundaries

The monitor consumes one symbol/arity token at a time. It rejects as soon
as a supplied prefix completes. An empty residual list has the behavior of
source `Free`. Initial empty prefixes reject before any token is read.

Residual lists give a finite semantic view of prefix continuations. This
module does not implement source Map/IntMap minimization, position IDs,
`endsOf`, transition-copy enumeration, or reachable FTA allocation.
-/
namespace MicroCFTA.SourceCurrentPrefixExclusion
open Language
variable {Token : Type}

/-- Source prefix words that still continue after one matching token. -/
def tails [DecidableEq Token] (token : Token) : List (List Token) → List (List Token)
  | [] => []
  | [] :: rest => tails token rest
  | (first :: suffix) :: rest => if first = token then suffix :: tails token rest else tails token rest

/-- Residual membership is exactly removal of one matching leading token. -/
theorem tails_member [DecidableEq Token] (token : Token) (paths : List (List Token)) (suffix : List Token) :
    suffix ∈ tails token paths ↔ token :: suffix ∈ paths := by
  induction paths with
  | nil => simp [tails]
  | cons path rest ih =>
      cases path with
      | nil => simp [tails, ih]
      | cons first path =>
          by_cases same : first = token
          · subst first; simp [tails, ih]
          · simp [tails, same, ih, Ne.symm same]

/-- Active continuations cannot already contain a completed empty word. -/
def Active (paths : List (List Token)) : Prop := [] ∉ paths

/-- Complete a prefix before any later token can change the answer. -/
def step [DecidableEq Token] (paths : List (List Token)) (token : Token) : Option (List (List Token)) :=
  let next := tails token paths
  if [] ∈ next then none else some next

/-- Scan finite tokens with one deterministic continuation state. -/
def scan [DecidableEq Token] (paths : List (List Token)) : List Token → Option (List (List Token))
  | [] => some paths
  | token :: rest => (step paths token).bind fun next => scan next rest

/-- The source root guard handles empty prefixes independently of `Free`. -/
def check [DecidableEq Token] (paths : List (List Token)) (word : List Token) : Option (List (List Token)) :=
  if [] ∈ paths then none else scan paths word

/-- A supplied word is a prefix of the complete consumed token stream. -/
def Forbidden (paths : List (List Token)) (word : List Token) : Prop :=
  ∃ path ∈ paths, path.IsPrefix word

/-- Before completion, one source token leaves exactly the matching suffix obligations. -/
theorem forbidden_cons [DecidableEq Token] (paths : List (List Token)) (token : Token) (word : List Token)
    (active : Active paths) : Forbidden paths (token :: word) ↔ Forbidden (tails token paths) word := by
  constructor
  · rintro ⟨path, member, starts⟩
    cases path with
    | nil => exact False.elim (active member)
    | cons first suffix =>
        obtain ⟨same, rest⟩ := List.cons_prefix_cons.mp starts
        subst first
        exact ⟨suffix, (tails_member token paths suffix).mpr member, rest⟩
  · rintro ⟨suffix, member, starts⟩
    exact ⟨token :: suffix, (tails_member token paths suffix).mp member, List.cons_prefix_cons.mpr ⟨rfl, starts⟩⟩

/-- Source token scanning rejects exactly when a nonempty active prefix completes. -/
theorem scan_none_iff [DecidableEq Token] (word : List Token) (paths : List (List Token)) (active : Active paths) :
    scan paths word = none ↔ Forbidden paths word := by
  induction word generalizing paths with
  | nil =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨path, member, starts⟩
        have empty : path = [] := List.prefix_nil.mp starts
        subst path
        exact False.elim (active member)
  | cons token rest ih =>
      by_cases completed : [] ∈ tails token paths
      · simp only [scan, step, completed, ite_true, Option.bind_none]
        constructor
        · intro _
          exact (forbidden_cons paths token rest active).mpr ⟨[], completed, List.nil_prefix⟩
        · intro _; trivial
      · simp only [scan, step, completed, ite_false, Option.bind_some]
        exact (ih (tails token paths) completed).trans (forbidden_cons paths token rest active).symm

/-- Root checking implements literal token-word prefix rejection, including empty words. -/
theorem check_none_iff [DecidableEq Token] (paths : List (List Token)) (word : List Token) :
    check paths word = none ↔ Forbidden paths word := by
  by_cases empty : [] ∈ paths
  · simp only [check, empty, ite_true]
    exact ⟨fun _ => ⟨[], empty, List.nil_prefix⟩, fun _ => trivial⟩
  · simpa only [check, empty, ite_false] using scan_none_iff word paths empty

/-- A finite word is retained exactly when none of the supplied words is its prefix. -/
theorem check_success_iff [DecidableEq Token] (paths : List (List Token)) (word : List Token) :
    (∃ final, check paths word = some final) ↔ ∀ path ∈ paths, ¬path.IsPrefix word := by
  constructor
  · rintro ⟨final, done⟩ path member starts
    have rejected := (check_none_iff paths word).mpr ⟨path, member, starts⟩
    rw [done] at rejected
    cases rejected
  · intro absent
    cases done : check paths word with
    | some final => exact ⟨final, rfl⟩
    | none =>
        obtain ⟨path, member, starts⟩ := (check_none_iff paths word).mp done
        exact False.elim (absent path member starts)

/-- Empty prefix sets behave as source `Free` for every following token. -/
theorem scan_free [DecidableEq Token] (word : List Token) : scan ([] : List (List Token)) word = some [] := by
  induction word with
  | nil => rfl
  | cons token rest ih => simpa only [scan, step, tails, List.not_mem_nil, ite_false, Option.bind_some] using ih

/-- Any initial empty prefix rejects even an empty input stream. -/
theorem empty_rejects [DecidableEq Token] (paths : List (List Token)) (word : List Token)
    (empty : [] ∈ paths) : check paths word = none := by simp only [check, empty, ite_true]

/-- A completed scan retains an active continuation state. -/
theorem scan_active [DecidableEq Token] (paths final : List (List Token)) (word : List Token)
    (active : Active paths) (done : scan paths word = some final) : Active final := by
  induction word generalizing paths with
  | nil => cases done; exact active
  | cons token rest ih =>
      simp only [scan, step] at done
      split at done
      · cases done
      · rename_i notCompleted
        exact ih _ notCompleted done

/-- Token concatenation uses exactly the state returned by the preceding tokens. -/
theorem scan_append [DecidableEq Token] (paths : List (List Token)) (first second : List Token) :
    scan paths (first ++ second) = (scan paths first).bind fun middle => scan middle second := by
  induction first generalizing paths with
  | nil => rfl
  | cons token rest ih =>
      simp only [List.cons_append, scan]
      cases moved : step paths token with
      | none => rfl
      | some next => simpa only [Option.bind_some] using ih next

/-- Longest remaining prefix depth is finite even when the input FTA has cycles. -/
def depth : List (List Token) → Nat
  | [] => 0
  | path :: paths => max path.length (depth paths)

/-- Prefix depth is the maximum length of its finite stored paths. -/
theorem depth_le (paths : List (List Token)) (bound : Nat) :
    depth paths ≤ bound ↔ ∀ path ∈ paths, path.length ≤ bound := by
  induction paths with
  | nil => simp [depth]
  | cons path paths ih => simp [depth, ih, Nat.max_le]

/-- Each nonfree continuation consumes one unit of the prefix automaton's finite depth. -/
theorem tails_depth_lt [DecidableEq Token] (token : Token) (paths : List (List Token))
    (nonfree : tails token paths ≠ []) : depth (tails token paths) < depth paths := by
  obtain ⟨first, rest, shape⟩ := List.exists_cons_of_ne_nil nonfree
  have member : first ∈ tails token paths := by simp [shape]
  have old : token :: first ∈ paths := (tails_member token paths first).mp member
  have positive := (depth_le paths (depth paths)).mp (Nat.le_refl _) (token :: first) old
  have bounded : depth (tails token paths) ≤ depth paths - 1 := by
    apply (depth_le _ _).mpr
    intro suffix included
    have original := (tails_member token paths suffix).mp included
    have sized := (depth_le paths (depth paths)).mp (Nat.le_refl _) (token :: suffix) original
    simp only [List.length_cons] at sized
    omega
  simp only [List.length_cons] at positive
  omega

/-- Source preorder tokens retain both the symbol and the actual child count. -/
abbrev NodeToken (Symbol : Type) := Symbol × Int

mutual
  /-- A finite term starts with its root token and then each child in source order. -/
  def preorder : Term Symbol → List (NodeToken Symbol)
    | .node symbol children => (symbol, Int.ofNat children.length) :: forestPreorder children
  termination_by term => sizeOf term

  /-- A child forest contributes each complete child preorder in its original order. -/
  def forestPreorder : List (Term Symbol) → List (NodeToken Symbol)
    | [] => []
    | first :: rest => preorder first ++ forestPreorder rest
  termination_by terms => sizeOf terms
end

/-- Forest preorder is the literal concatenation of its ordered child token streams. -/
theorem forestPreorder_eq (children : List (Term Symbol)) :
    forestPreorder children = (children.map preorder).flatten := by
  induction children with
  | nil => simp [forestPreorder]
  | cons first rest ih => simp only [forestPreorder, List.map_cons, List.flatten_cons, ih]

/-- Every token emitted by a finite term has a nonnegative source arity. -/
theorem preorder_nonnegative (term : Term Symbol) :
    ∀ token ∈ preorder term, 0 ≤ token.2 := by
  induction term using Term.rec
      (motive_2 := fun children : List (Term Symbol) =>
        ∀ token ∈ forestPreorder children, 0 ≤ token.2) with
  | node symbol children ih =>
      intro token member
      rw [preorder] at member
      rcases List.mem_cons.mp member with same | below
      · subst token
        exact Int.natCast_nonneg _
      · exact ih token below
  | nil => simp_all [forestPreorder]
  | cons first rest firstChecked restChecked =>
      rename_i token member
      rw [forestPreorder] at member
      rcases List.mem_append.mp member with member | member
      · exact firstChecked token member
      · exact restChecked token member

/-- A literal negative-arity word cannot be a prefix of a finite term's preorder. -/
theorem negative_token_not_prefix (term : Term Symbol) (path : List (NodeToken Symbol))
    (token : NodeToken Symbol) (member : token ∈ path) (negative : token.2 < 0) :
    ¬path.IsPrefix (preorder term) := by
  rintro ⟨rest, same⟩
  have included : token ∈ preorder term := same ▸ List.mem_append_left rest member
  have nonnegative := preorder_nonnegative term token included
  omega

/-- Exact child boundaries retain the actual deterministic state after each complete child. -/
inductive Boundaries [DecidableEq Token] : List (List Token) → List (List Token) →
    List (List (List Token)) → List (List Token) → Prop where
  | nil (paths : List (List Token)) : Boundaries paths [] [] paths
  | cons (done : scan paths word = some middle) (later : Boundaries middle words endings final) :
      Boundaries paths (word :: words) (middle :: endings) final

/-- Every child-boundary receipt consumes exactly the concatenated source token streams. -/
theorem Boundaries.scan [DecidableEq Token] {paths final : List (List Token)}
    {words : List (List Token)} {endings : List (List (List Token))}
    (actual : Boundaries paths words endings final) : scan paths words.flatten = some final := by
  induction actual with
  | nil => rfl
  | cons done _ ih => simp only [List.flatten_cons, scan_append, done, Option.bind_some, ih]

/-- Every successful ordered forest scan derives its intermediate child boundaries. -/
theorem boundaries_of_scan [DecidableEq Token] (words : List (List Token)) (paths final : List (List Token))
    (done : scan paths words.flatten = some final) : ∃ endings, Boundaries paths words endings final := by
  induction words generalizing paths with
  | nil => cases done; exact ⟨[], .nil _⟩
  | cons word words ih =>
      rw [List.flatten_cons, scan_append] at done
      cases first : scan paths word with
      | none => rw [first] at done; cases done
      | some middle =>
          rw [first] at done
          obtain ⟨endings, later⟩ := ih middle done
          exact ⟨middle :: endings, .cons first later⟩

/-- A term fixes every intermediate child position and its final position. -/
theorem Boundaries.unique [DecidableEq Token] {paths firstFinal secondFinal : List (List Token)}
    {words : List (List Token)} {firstEnds secondEnds : List (List (List Token))}
    (first : Boundaries paths words firstEnds firstFinal) (second : Boundaries paths words secondEnds secondFinal) :
    firstEnds = secondEnds ∧ firstFinal = secondFinal := by
  induction first generalizing secondEnds secondFinal with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons done later ih =>
      cases second with
      | cons other tail =>
          have same := Option.some.inj (done.symm.trans other)
          subst same
          obtain ⟨equal, final⟩ := ih tail
          exact ⟨congrArg (_ :: ·) equal, final⟩

/-- Each actual child has exactly one recorded boundary. -/
theorem Boundaries.length [DecidableEq Token] {paths final : List (List Token)}
    {words : List (List Token)} {endings : List (List (List Token))}
    (actual : Boundaries paths words endings final) : endings.length = words.length := by
  induction actual with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

/-- Successful term-root scanning derives the exact ordered boundaries of all original children. -/
theorem node_boundaries [DecidableEq Symbol] (paths : List (List (NodeToken Symbol)))
    (symbol : Symbol) (children : List (Term Symbol)) (final : List (List (NodeToken Symbol)))
    (done : scan paths (preorder (.node symbol children)) = some final) :
    ∃ start endings, step paths (symbol, Int.ofNat children.length) = some start ∧
      Boundaries start (children.map preorder) endings final := by
  simp only [preorder, scan] at done
  cases moved : step paths (symbol, Int.ofNat children.length) with
  | none => rw [moved] at done; cases done
  | some start =>
      rw [moved] at done
      rw [forestPreorder_eq] at done
      obtain ⟨endings, actual⟩ := boundaries_of_scan (children.map preorder) start final done
      exact ⟨start, endings, rfl, actual⟩

end MicroCFTA.SourceCurrentPrefixExclusion
