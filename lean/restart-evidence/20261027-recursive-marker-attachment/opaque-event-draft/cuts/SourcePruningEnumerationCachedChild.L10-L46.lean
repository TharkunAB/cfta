/-- Allocate the raw slot, update its native flag and inherit ancestry once. -/
def allocate
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (node : Option Nat) (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  (SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated node [])).map fun flag =>
    (before.core.counter,
      ⟨EnumerationState.allocated node before.core,
        fun slot => if flag then
          if slot = before.core.counter then true else before.expandable slot
          else before.expandable slot,
        before.waiting⟩)

/-- Read the old raw slot before the native full-constraint write. -/
def writeSlot
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : EnumerationState.UVarValue Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  (before.core.values[target]?).bind fun old =>
    SourcePruningEnumerationNativeIndex.write heap fuel target value
      (references value) (references old) before

/-- Execute the ordinary nonterminal child branch with both native indexes. -/
def prepareOrdinary
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (scs : List EnumerationState.Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  match value with
  | .node _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
      else
        (encodeNode value).bind fun handle =>
          (allocate heap (some handle) before).bind fun allocation =>
            (writeSlot heap fuel allocation.1 (.unenumerated (some handle) scs) allocation.2).map
