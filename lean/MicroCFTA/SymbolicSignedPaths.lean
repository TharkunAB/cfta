import MicroCFTA.SymbolicEqualityBridge
import MicroCFTA.TermOperations

/-!
# Signed source paths and safe symbolic path encoding

Haskell child indices are signed. A negative index has no selected subtree.
The equality smart constructor rejects such paths before interning a positive
path class. Reflexive and negated guards can retain signed paths, so their
conversion to the natural-index symbolic model needs a separate bound.
-/
namespace MicroCFTA.SymbolicSignedPaths
open Language

abbrev Path := List Int

/-- Lookup follows the source signed child access at every path step. -/
def lookup : Term Symbol → Path → Option (Term Symbol)
  | term, [] => some term
  | .node _ children, index :: rest =>
      if index < 0 then none else children[index.toNat]?.bind fun child => lookup child rest

/-- A path decodes to natural indices only when every signed index is nonnegative. -/
def decode : Path → Option (List Nat)
  | [] => some []
  | index :: rest => if index < 0 then none else (decode rest).map (index.toNat :: ·)

/-- Signed lookup is exactly natural lookup after successful path decoding. -/
theorem lookup_decode (term : Term Symbol) (path : Path) :
    lookup term path = (decode path).bind term.atPath := by
  induction path generalizing term with
  | nil => rfl
  | cons index rest ih =>
    cases term with
    | node symbol children =>
      by_cases negative : index < 0
      · simp [lookup, decode, negative]
      · simp only [lookup, decode, negative, ↓reduceIte]
        cases child : children[index.toNat]? with
        | none => cases decode rest <;> simp [child, Term.atPath]
        | some value =>
          rw [Option.bind_some, ih]
          cases decode rest <;> simp [child, Term.atPath]

/-- A successful decoded path contains only nonnegative source indices. -/
theorem decode_nonnegative (path : Path) (natural : List Nat) (success : decode path = some natural) :
    ∀ index ∈ path, 0 ≤ index := by
  induction path generalizing natural with
  | nil => intro index member; cases member
  | cons first rest ih =>
    simp only [decode] at success
    split at success
    next negative => cases success
    next nonnegative =>
      cases decoded : decode rest with
      | none => simp [decoded] at success
      | some tail =>
        intro index member
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · exact ih tail decoded index member

/-- The exact source arity test accepts empty paths and checks every signed index. -/
def fitsPath (arity : Nat) (path : Path) : Bool :=
  match path with
  | [] => true
  | first :: _ => decide (first < (arity : Int)) && path.all (fun index => decide (0 ≤ index))

/-- Every existing subtree passes the source path arity test at its root. -/
theorem lookup_fitsPath (symbol : Symbol) (children : List (Term Symbol)) (path : Path) (part : Term Symbol)
    (found : lookup (.node symbol children) path = some part) : fitsPath children.length path = true := by
  have nonnegative : ∀ index ∈ path, 0 ≤ index := by
    rw [lookup_decode] at found
    cases decoded : decode path with
    | none => simp [decoded] at found
    | some natural => exact decode_nonnegative path natural decoded
  cases path with
  | nil => rfl
  | cons first rest =>
    have positive := nonnegative first (by simp)
    have childExists : children[first.toNat]? ≠ none := by
      intro absent
      simp [lookup, show ¬first < 0 by omega, absent] at found
    have bound : first.toNat < children.length := by
      by_cases inside : first.toNat < children.length
      · exact inside
      · exact False.elim (childExists (List.getElem?_eq_none (by omega)))
    have signedBound : first < (children.length : Int) := by omega
    simp only [fitsPath, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨signedBound, nonnegative⟩

/-- The common-subtree meaning of one signed class. -/
def ClassHolds (term : Term Symbol) : List Path → Prop
  | [] => True
  | first :: rest => ∃ value, lookup term first = some value ∧ ∀ path ∈ rest, lookup term path = some value

/-- Every class path has a common selected subtree. -/
theorem class_lookup (term : Term Symbol) (paths : List Path) (holds : ClassHolds term paths)
    (path : Path) (member : path ∈ paths) : ∃ value, lookup term path = some value := by
  cases paths with
  | nil => cases member
  | cons first rest =>
    obtain ⟨value, head, tail⟩ := holds
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨value, head⟩
    · exact ⟨value, tail path member⟩

/-- The source `fitsArity` test, including its contradictory-equality case. -/
def fitsArity (arity : Nat) : Option (List (List Path)) → Bool
  | none => false
  | some classes => classes.all fun paths => paths.all (fitsPath arity)

/-- Complete signed equality semantics for normalized source classes. -/
def EqualitiesHold (term : Term Symbol) : Option (List (List Path)) → Prop
  | none => False
  | some classes => ∀ paths ∈ classes, ClassHolds term paths

/-- A failed source arity check rejects no valid equality-constrained term. -/
theorem fitsArity_reject (symbol : Symbol) (children : List (Term Symbol)) (classes : Option (List (List Path)))
    (rejected : fitsArity children.length classes = false) : ¬ EqualitiesHold (.node symbol children) classes := by
  intro holds
  cases classes with
  | none => exact holds
  | some classes =>
    have fits : fitsArity children.length (some classes) = true := by
      simp only [fitsArity, List.all_eq_true]
      intro paths present path member
      obtain ⟨value, found⟩ := class_lookup _ paths (holds paths present) path member
      exact lookup_fitsPath symbol children path value found
    simp [rejected] at fits

/-- Every constructor in this finite term has at most the given number of children. -/
inductive ArityBound (bound : Nat) : Term Symbol → Prop where
  | node (symbol : Symbol) (children : List (Term Symbol)) : children.length ≤ bound →
      (∀ child ∈ children, ArityBound bound child) → ArityBound bound (.node symbol children)

/-- Preserve nonnegative positions and map negative positions to an impossible child index. -/
def encode (bound : Nat) (path : Path) : List Nat :=
  path.map fun index => if index < 0 then bound else index.toNat

/-- The bounded encoding preserves lookup exactly, including negative path segments. -/
theorem encode_lookup (bound : Nat) (term : Term Symbol) (bounded : ArityBound bound term) (path : Path) :
    term.atPath (encode bound path) = lookup term path := by
  induction path generalizing term with
  | nil => rfl
  | cons index rest ih =>
    cases bounded with
    | node symbol children arity childBounds =>
      by_cases negative : index < 0
      · simp [encode, lookup, negative, Term.atPath, List.getElem?_eq_none arity]
      · simp only [encode, List.map_cons, negative, ↓reduceIte, Term.atPath, lookup]
        cases found : children[index.toNat]? with
        | none => rfl
        | some child =>
          exact ih child (childBounds child (List.mem_of_getElem? found))

/-- The signed class compiler can use natural paths after the arity-bound encoding. -/
theorem encode_class (bound : Nat) (term : Term Symbol) (bounded : ArityBound bound term) (paths : List Path) :
    Symbolic.ClassSatisfied term (paths.map (encode bound)) ↔ ClassHolds term paths := by
  cases paths with
  | nil => rfl
  | cons first rest =>
    simp only [List.map_cons, Symbolic.ClassSatisfied, ClassHolds, encode_lookup bound term bounded, List.mem_map]
    constructor
    · rintro ⟨value, head, tail⟩
      exact ⟨value, head, fun path present => by
        have found := tail (encode bound path) ⟨path, present, rfl⟩
        simpa only [encode_lookup bound term bounded] using found⟩
    · rintro ⟨value, head, tail⟩
      refine ⟨value, head, ?_⟩
      rintro path ⟨original, present, rfl⟩
      simpa only [encode_lookup bound term bounded] using tail original present

/-- A constructor-row arity bound is inherited by every accepted subtree. -/
theorem accepted_arityBound (automaton : Automaton State Symbol) (bound : Nat)
    (arity : ∀ state edge, edge ∈ automaton state → edge.children.length ≤ bound)
    (state : State) (term : Term Symbol) (accepted : Accepts automaton state term) : ArityBound bound term := by
  induction accepted using Accepts.rec
    (motive_2 := fun _ terms _ => ∀ term ∈ terms, ArityBound bound term) with
  | node edge children member runs _ ih =>
    exact .node edge.label children (by rw [← runs.length_eq]; exact arity _ edge member) ih
  | nil => rename_i term member; cases member
  | cons head tail first rest =>
    rename_i term member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact rest term member

/-- Existing nonnegative paths decode without changing any index. -/
theorem decode_nonnegative_exact (path : Path) (nonnegative : ∀ index ∈ path, 0 ≤ index) :
    decode path = some (path.map Int.toNat) := by
  induction path with
  | nil => rfl
  | cons first rest ih =>
    have positive := nonnegative first (by simp)
    have tail := ih (fun index member => nonnegative index (by simp [member]))
    simp [decode, show ¬first < 0 by omega, tail]

/-- A successful arity check certifies the ordinary natural-index encoding for every class path. -/
theorem fitsArity_decodes (arity : Nat) (classes : List (List Path))
    (fits : fitsArity arity (some classes) = true)
    (paths : List Path) (present : paths ∈ classes) (path : Path) (member : path ∈ paths) :
    decode path = some (path.map Int.toNat) := by
  have fits := (List.all_eq_true.mp fits) paths present
  have fits := (List.all_eq_true.mp fits) path member
  apply decode_nonnegative_exact
  cases path with
  | nil => simp
  | cons first rest =>
    have positive := (Bool.and_eq_true _ _).mp fits |>.2
    simpa only [List.all_eq_true, decide_eq_true_eq] using positive

/-- Packed source path lookup uses the source signed child operation at every step. -/
def packedLookup (term : TermRepresentation.Packed Symbol) : Path → Option (TermRepresentation.Packed Symbol)
  | [] => some term
  | index :: rest => (TermOperations.signedChild index term).bind fun child => packedLookup child rest

/-- The packed storage path implementation has exactly the signed tree interpretation. -/
theorem packedLookup_exact (term : TermRepresentation.Packed Symbol) (path : Path) :
    (packedLookup term path).map TermRepresentation.unpack = lookup (TermRepresentation.unpack term) path := by
  induction path generalizing term with
  | nil => rfl
  | cons index rest ih =>
    rw [TermRepresentation.unpack_views term]
    by_cases negative : index < 0
    · simp [packedLookup, TermOperations.signedChild, lookup, negative]
    · simp only [packedLookup, TermOperations.signedChild, lookup, negative, ↓reduceIte]
      rw [← TermRepresentation.child_unpack]
      cases found : TermRepresentation.child term index.toNat with
      | none => rfl
      | some child => exact ih child

/-- A negative reflexive guard has no existing target, even though its two paths are identical. -/
theorem negative_reflexive_reject (term : Term Symbol) (index : Int) (negative : index < 0) (rest : Path) :
    ¬ ClassHolds term [index :: rest, index :: rest] := by
  cases term with
  | node symbol children => simp [ClassHolds, lookup, negative]

/-- Converting a negative index with `toNat` alone changes the lookup result. -/
theorem blind_toNat_changes_lookup :
    lookup (.node (0 : Nat) [.node 1 []]) [-1] = none ∧
      (Term.node (0 : Nat) [.node 1 []]).atPath ([-1].map Int.toNat) = some (.node 1 []) := by
  decide

end MicroCFTA.SymbolicSignedPaths
