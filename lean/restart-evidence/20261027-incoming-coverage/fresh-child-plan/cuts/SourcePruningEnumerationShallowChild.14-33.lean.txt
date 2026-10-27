/-- Prepare the supported nonterminal child branches from their complete native value. -/
def prepareChild (scs : List EnumerationState.Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard) :
    Option (EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
 :=
  match value with
  | .empty => some reject
  | .reference _ => none
  | .node _ _ _ _ | .union _ _ _ _ | .mu _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
        none
      else
        match encodeNode value with
        | none => none
        | some node =>
            some (allocate (some node) >>= fun uv =>
              match value with
              | .node _ _ _ _ =>
                  setValue uv (.unenumerated (some node) scs) >>= fun _ => pure (.hole uv)
              | _ => pure (.hole uv))
