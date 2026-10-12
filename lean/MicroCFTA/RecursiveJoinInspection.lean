import MicroCFTA.RecursiveJoinSupportFamily

/-!
# Diagnostic graph assembly for recursive joins

Inspection names are separate from semantic support. Source constructors
retain names on existing operands and attach each argument's name to both
copies of its join key. The diagnostic family uses a separate shared binder.
-/
namespace MicroCFTA.RecursiveJoinInspection
open Language GeneratorCombinators BinderLanguage SupportGraph
open RecursiveCallbackTermination (EngineTerm)

/-- A diagnostic edge retains its complete original payload and its optional display name. -/
structure Info (Symbol : Type) where
  original : Payload (Label Symbol)
  display : Option String

/-- Diagnostic names remain part of edge identity in the unreduced graph. -/
abbrev Graph (Symbol : Type) := Binding.Shape (Info Symbol)

/-- Add names while preserving every source child, constraint, and recursive reference. -/
def annotate (name : Label Symbol → Option String) : Support Symbol → Graph Symbol
  | .empty => .empty
  | .ref token => .ref token
  | .branch payload children => .branch ⟨payload, name payload.label⟩ (children.map (annotate name))
  | .alternatives alternatives => .alternatives (alternatives.map (annotate name))
  | .binder token body => .binder token (annotate name body)

/-- Forget diagnostic labels while preserving graph structure and predicates. -/
def erase : Graph Symbol → Support Symbol
  | .empty => .empty
  | .ref token => .ref token
  | .branch info children => .branch info.original (children.map erase)
  | .alternatives alternatives => .alternatives (alternatives.map erase)
  | .binder token body => .binder token (erase body)

/-- Plain inspection changes no underlying support field, including nested binders. -/
theorem erase_annotate (name : Label Symbol → Option String) (source : Support Symbol) :
    erase (annotate name source) = source := by
  induction source using Binding.Shape.rec
    (motive_2 := fun sources => (sources.map (annotate name)).map erase = sources) with
  | empty | ref token => simp only [annotate, erase]
  | branch payload children ih => simp only [annotate, erase]; rw [ih]
  | alternatives alternatives ih => simp only [annotate, erase]; rw [ih]
  | binder token body ih => simp only [annotate, erase]; rw [ih]
  | nil => rfl
  | cons first rest ih ir => simp only [List.map_cons, ih, ir]

/-- Construct one plain diagnostic edge and preserve its complete child list. -/
def edge (label : Label Symbol) (children : List (Graph Symbol)) : Graph Symbol :=
  .branch ⟨⟨label, fun _ => True⟩, none⟩ children

/-- The optional name of a joined argument appears on both copies of its positional key. -/
def key (component position : Nat) (name : Option String) : Graph Symbol :=
  .branch ⟨⟨.argKey component position, fun _ => True⟩, name⟩ []

/-- Labels whose complete graph is retained as one child by source closing. -/
def Ordinary (label : Label Symbol) : Prop := SupportClosing.ordinary label = true

/-- Outer diagnostic layers retain the source cases used by label and spine closing. -/
inductive Layer (Symbol : Type) where
  | pure
  | ordinary (graph : Graph Symbol)
  | ap (functions arguments : Layer Symbol)
  | choice (alternatives : List (Layer Symbol))
  | join (component : Nat) (operation : Layer Symbol) (arguments : List (Option String × Layer Symbol))

/-- An opaque diagnostic graph has no private outer root recognized by source closing. -/
def OrdinaryGraph : Graph Symbol → Prop
  | .empty | .ref _ => True
  | .binder .. => False
  | .branch info _ => Ordinary info.original.label
  | .alternatives roots => ∀ root ∈ roots, OrdinaryGraph root

/-- Every retained layer descriptor selects the same closing case as the source graph. -/
def Valid : Layer Symbol → Prop
  | .pure => True
  | .ordinary source => OrdinaryGraph source
  | .ap functions arguments => Valid functions ∧ Valid arguments
  | .choice alternatives => ∀ layer ∈ alternatives, Valid layer
  | .join _ operation arguments => Valid operation ∧ ∀ argument ∈ arguments, Valid argument.2
termination_by layer => sizeOf layer
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact Nat.lt_trans (List.sizeOf_lt_of_mem ‹_ ∈ _›) (by omega)
    | (rename_i argument member; have bound := List.sizeOf_lt_of_mem member; cases argument; simp_all; omega)

mutual
/-- The diagnostic graph contains the same source private constructors before closing. -/
def graph : Layer Symbol → Graph Symbol
  | .pure => edge .pure []
  | .ordinary source => source
  | .ap functions arguments => edge .apply [graph functions, graph arguments]
  | .choice alternatives => .alternatives (alternatives.attach.mapIdx fun index body => edge (.choice index) [graph body.val])
  | .join component operation arguments =>
      .branch ⟨⟨.joinN, fun term => ∀ index < arguments.length, PathsEqual term [0, index + 1] [index + 1, 0]⟩, none⟩
        (edge .centerKeyed (graph operation :: keys component 0 arguments) :: argumentNodes component 0 arguments)
termination_by layer => sizeOf layer
decreasing_by all_goals simp_wf; all_goals first | omega | (have := List.sizeOf_lt_of_mem body.property; omega)

/-- Source key names come from the argument at the same position. -/
def keys (component first : Nat) : List (Option String × Layer Symbol) → List (Graph Symbol)
  | [] => []
  | (name, _) :: rest => key component first name :: keys component (first + 1) rest

/-- Every diagnostic argument keeps its positional key before its original graph. -/
def argumentNodes (component first : Nat) : List (Option String × Layer Symbol) → List (Graph Symbol)
  | [] => []
  | (name, argument) :: rest => edge .argKeyed [key component first name, graph argument] :: argumentNodes component (first + 1) rest
termination_by arguments => sizeOf arguments
decreasing_by all_goals simp_wf; all_goals omega
end

/-- Source application flattening retains ordinary, choice, and join roots as one child. -/
def prefixes : Layer Symbol → List (Graph Symbol)
  | .pure => []
  | .ap functions arguments => prefixes functions ++ [graph arguments]
  | layer => [graph layer]

/-- Source label closing retains complete predicates and removes only recognized private scaffolding. -/
def closeRoots (symbol : Symbol) : Layer Symbol → List (Graph Symbol)
  | .pure => [edge (.user symbol) []]
  | .ordinary source => [edge (.user symbol) [source]]
  | .ap functions arguments => [edge (.user symbol) (prefixes functions ++ [graph arguments])]
  | .choice alternatives =>
      if alternatives.isEmpty then [edge (.user symbol) [graph (.choice [])]]
      else alternatives.flatMap (closeRoots symbol)
  | .join component operation arguments =>
      [.branch ⟨⟨.user symbol, fun term => ∀ index < arguments.length, PathsEqual term [0, index + 1] [index + 1, 0]⟩, none⟩
        (edge .centerKeyed (graph operation :: keys component 0 arguments) :: argumentNodes component 0 arguments)]

/-- Every emitted closed root has an ordinary user label with its original predicate. -/
theorem closeRoots_ordinary (symbol : Symbol) (layer : Layer Symbol) :
    ∀ root ∈ closeRoots symbol layer, OrdinaryGraph root := by
  cases layer with
  | pure | ordinary source | ap functions arguments | join component operation arguments =>
      intro root member
      simp only [closeRoots, List.mem_singleton] at member
      subst root
      simp only [edge, OrdinaryGraph, Ordinary, SupportClosing.ordinary]
  | choice alternatives =>
      cases alternatives with
      | nil =>
          intro root member
          simp only [closeRoots, List.isEmpty_nil, ↓reduceIte, List.mem_singleton] at member
          subst root
          simp only [edge, OrdinaryGraph, Ordinary, SupportClosing.ordinary]
      | cons first rest =>
        intro root member
        simp only [closeRoots, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at member
        obtain ⟨child, present, found⟩ := List.mem_flatMap.mp member
        exact closeRoots_ordinary symbol child root found
termination_by sizeOf layer
decreasing_by have bound := List.sizeOf_lt_of_mem present; simp_wf; simp_all; omega

/-- Each inspectable generator keeps an optional name and the independent diagnostic layer. -/
structure Inspection (Symbol : Type) where
  name : Option String
  layer : Layer Symbol

/-- Read the actual diagnostic graph retained by a source inspection record. -/
def Inspection.graph (inspection : Inspection Symbol) : Graph Symbol := RecursiveJoinInspection.graph inspection.layer

/-- Named groups change only the optional name read by surrounding constructors. -/
def named (name : Option String) (inspection : Inspection Symbol) : Inspection Symbol := {inspection with name}

/-- Choice retains a name only when the complete alternative list has the same name. -/
def commonName : List (Option String) → Option String
  | [] => none
  | first :: rest => if rest.all (· == first) then first else none

/-- Source choice fixes original branch indices before it inspects the common name. -/
def choice (alternatives : List (Inspection Symbol)) : Inspection Symbol :=
  ⟨commonName (alternatives.map (·.name)), .choice (alternatives.map (·.layer))⟩

/-- Value maps and pay leave the complete diagnostic record unchanged. -/
def preserve (inspection : Inspection Symbol) : Inspection Symbol := inspection

/-- Source application clears the outer name and keeps both operand graphs. -/
def ap (functions arguments : Inspection Symbol) : Inspection Symbol := ⟨none, .ap functions.layer arguments.layer⟩

/-- Source labelling keeps the group's name and closes its actual diagnostic layer. -/
def label (symbol : Symbol) (inspection : Inspection Symbol) : Inspection Symbol :=
  ⟨inspection.name, .ordinary (.alternatives (closeRoots symbol inspection.layer))⟩

/-- A source join clears its result name and names only the positional equality witnesses. -/
def join (component : Nat) (operation : Inspection Symbol) (arguments : List (Inspection Symbol)) : Inspection Symbol :=
  ⟨none, .join component operation.layer (arguments.map fun argument => (argument.name, argument.layer))⟩

/-- Labelling produces a valid ordinary layer and retains the diagnostic name. -/
theorem label_valid (symbol : Symbol) (inspection : Inspection Symbol) : Valid (label symbol inspection).layer := by
  simp only [label, Valid, OrdinaryGraph]
  exact closeRoots_ordinary symbol inspection.layer

/-- Choice propagates exactly the validity of its original child descriptors. -/
theorem choice_valid (alternatives : List (Inspection Symbol))
    (valid : ∀ inspection ∈ alternatives, Valid inspection.layer) : Valid (choice alternatives).layer := by
  simp only [choice, Valid]
  intro layer member
  obtain ⟨inspection, present, rfl⟩ := List.mem_map.mp member
  exact valid inspection present

/-- The joined graph needs no new outer-root condition beyond its operand descriptors. -/
theorem join_valid (component : Nat) (operation : Inspection Symbol) (arguments : List (Inspection Symbol))
    (operationValid : Valid operation.layer) (argumentsValid : ∀ argument ∈ arguments, Valid argument.layer) :
    Valid (join component operation arguments).layer := by
  simp only [join, Valid]
  refine ⟨operationValid, ?_⟩
  intro argument member
  obtain ⟨inspection, present, rfl⟩ := List.mem_map.mp member
  exact argumentsValid inspection present

/-- Each declared argument has exactly one center key and one keyed argument edge. -/
theorem keys_length (component first : Nat) (arguments : List (Option String × Layer Symbol)) :
    (keys component first arguments).length = arguments.length ∧
    (argumentNodes component first arguments).length = arguments.length := by
  induction arguments generalizing first with
  | nil => simp [keys, argumentNodes]
  | cons argument rest ih =>
      rcases argument with ⟨name, argument⟩
      simp only [keys, argumentNodes, List.length_cons, (ih (first + 1)).1, (ih (first + 1)).2]
      trivial

/-- Key lookup uses the source argument name at the same component and position. -/
theorem keys_lookup (component first : Nat) (arguments : List (Option String × Layer Symbol))
    (position : Nat) (inside : position < arguments.length) :
    (keys component first arguments)[position]? = some (key component (first + position) arguments[position].1) := by
  induction arguments generalizing first position with
  | nil => simp at inside
  | cons argument rest ih =>
      cases position with
      | zero => simp [keys]
      | succ position => simpa [keys, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first + 1) position (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside)

/-- Both ends of every join equality retain the same exact named key node. -/
theorem arguments_lookup (component first : Nat) (arguments : List (Option String × Layer Symbol))
    (position : Nat) (inside : position < arguments.length) :
    (argumentNodes component first arguments)[position]? =
      some (edge .argKeyed [key component (first + position) arguments[position].1, graph arguments[position].2]) := by
  induction arguments generalizing first position with
  | nil => simp at inside
  | cons argument rest ih =>
      rcases argument with ⟨name, argument⟩
      cases position with
      | zero => simp [argumentNodes]
      | succ position => simpa [argumentNodes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first + 1) position (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside)

/-- Diagnostic names cannot change the original label or payload of an equality witness. -/
theorem erase_key (component position : Nat) (name : Option String) :
    erase (key (Symbol := Symbol) component position name) = SupportGraph.singleton (.node (.argKey component position) []) := by
  simp [key, erase, SupportGraph.singleton, SupportGraph.edge]

/-- Erasure retains the original ordered join key list. -/
theorem erase_keys (component first : Nat) (arguments : List (Option String × Layer Symbol)) :
    (keys component first arguments).map erase = (SupportJoin.keys component first arguments.length).map singleton := by
  induction arguments generalizing first with
  | nil => rfl
  | cons argument rest ih => simp only [keys, List.map_cons, erase_key, List.length_cons, SupportJoin.keys, ih]

/-- Erasure retains each argument graph and its original positional wrapper. -/
theorem erase_arguments (component first : Nat) (arguments : List (Option String × Layer Symbol)) :
    (argumentNodes component first arguments).map erase =
      SupportJoin.argumentNodes component first (arguments.map fun argument => erase (graph argument.2)) := by
  induction arguments generalizing first with
  | nil => simp [argumentNodes, SupportJoin.argumentNodes]
  | cons argument rest ih =>
      rcases argument with ⟨name, argument⟩
      simp only [argumentNodes, List.map_cons, erase, edge, erase_key, List.map_nil, SupportJoin.argumentNodes, ih, SupportGraph.edge, SupportGraph.singleton]

/-- The unreduced diagnostic join erases to the exact semantic join constructor. -/
theorem erase_join (component : Nat) (operation : Inspection Symbol) (arguments : List (Inspection Symbol)) :
    erase (join component operation arguments).graph =
      SupportJoin.joinNode component (erase operation.graph) (arguments.map fun argument => erase argument.graph) := by
  simp only [join, Inspection.graph, graph, erase, List.map_cons, List.map_map, erase_keys, erase_arguments,
    edge, SupportGraph.edge, SupportJoin.joinNode, List.length_map, Function.comp_def]

/-- The family names its selected key in both the AtKey restriction and Family edge. -/
def familyKey (position : Nat) (name : Option String) : Graph Symbol :=
  .branch ⟨⟨.key position, fun _ => True⟩, name⟩ []

/-- Diagnostic recursive occurrences read the separate inspection family reference. -/
def occurrence (token position : Nat) (name : Option String) : Inspection Symbol :=
  ⟨name, .ordinary (.branch ⟨⟨.atKey, fun term => PathsEqual term [0] [1, 0]⟩, none⟩
    [familyKey position name, .ref token])⟩

/-- The occurrence descriptor exposes AtKey and keeps the recursive reference as a child. -/
theorem occurrence_valid (token position : Nat) (name : Option String) :
    Valid (occurrence (Symbol := Symbol) token position name).layer := by
  simp [occurrence, Valid, OrdinaryGraph, Ordinary, SupportClosing.ordinary]

/-- A diagnostic key erases to the original source singleton key. -/
theorem erase_familyKey (position : Nat) (name : Option String) :
    erase (familyKey (Symbol := Symbol) position name) = SupportGraph.singleton (.node (.key position) []) := by
  simp [erase, familyKey, SupportGraph.singleton, SupportGraph.edge]

/-- Occurrence erasure preserves the exact private AtKey constraint and binder reference. -/
theorem erase_occurrence (token position : Nat) (name : Option String) :
    erase (occurrence (Symbol := Symbol) token position name).graph = restrictKey position (.ref token) := by
  simp [occurrence, Inspection.graph, graph, erase, erase_familyKey, restrictKey]

/-- The separate diagnostic knot uses the same keys and source bodies with their retained names. -/
def family (token : Nat) (code : Key → Nat) (keys : List Key) (names : Key → Option String)
    (build : (Key → Inspection Symbol) → Key → Inspection Symbol) : Graph Symbol :=
  .binder token (.alternatives (keys.map fun key => edge .family
    [familyKey (code key) (names key), (build (fun key => occurrence token (code key) (names key)) key).graph]))

/-- Erasure keeps the separate diagnostic knot and every exact Family key boundary. -/
theorem erase_family (token : Nat) (code : Key → Nat) (keys : List Key) (names : Key → Option String)
    (build : (Key → Inspection Symbol) → Key → Inspection Symbol) :
    erase (family token code keys names build) =
      .binder token (SupportGraph.family (keys.map fun key =>
        (code key, erase (build (fun key => occurrence token (code key) (names key)) key).graph))) := by
  simp only [family, erase, List.map_map, edge, List.map_cons, erase_familyKey,
    List.map_nil, SupportGraph.family, SupportGraph.edge, Function.comp_def]

/-- Closing an empty choice retains the source's unreachable labelled child in diagnostics. -/
theorem label_empty_choice (symbol : Symbol) :
    (label symbol (choice [])).graph = .alternatives [edge (.user symbol) [.alternatives []]] := by
  simp [label, choice, Inspection.graph, graph, closeRoots]

/-- Names remain independent of source label closing and join result names. -/
theorem name_fields (symbol : Symbol) (component : Nat) (operation : Inspection Symbol) (arguments : List (Inspection Symbol)) :
    (label symbol operation).name = operation.name ∧ (join component operation arguments).name = none ∧
    (ap operation operation).name = none := ⟨rfl, rfl, rfl⟩

/-- Concrete unequal group names remain attached to both copies of the appropriate join key. -/
theorem named_arguments :
    keys (Symbol := Nat) 3 0 [(some "flag", .pure), (some "value", .pure)] =
      [key 3 0 (some "flag"), key 3 1 (some "value")] ∧
    commonName [some "same", some "same"] = some "same" ∧
    commonName [some "first", some "second"] = none := by
  constructor
  · rfl
  · decide +kernel

end MicroCFTA.RecursiveJoinInspection
