theorem child_evidence
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (edge : EdgeValue Symbol Constraint)
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie)
    (fragments : List Fragment)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    (related : All₂ (fun (input : Node × List Suspended) (fragment : Fragment) =>
      InternedGuardedLanguage.meaning holds ambient input.1 (Fragments.fill assignment fragment) ∧
      ∀ sc ∈ (match input.1 with
        | .node _ _ _ _ => input.2
        | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
        Suspended.Holds assignment (Fragments.fill assignment fragment) sc)
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries) fragments) :
    InternedGuardedLanguage.forest holds ambient edge.children
      (fragments.map (Fragments.fill assignment)) ∧
      ∀ index child, (fragments.map (Fragments.fill assignment))[index]? = some child →
        ∀ sc ∈ descendScs index (scs ++ suspendedVars start tries),
