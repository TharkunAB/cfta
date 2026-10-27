def arityAllows (arity : Nat) (scs : List Suspended) : Bool :=
  scs.all fun sc => (EqualityTrie.fromPathTrie sc.trie).all fun path =>
    match path with | [] => true | child :: _ => decide (child < arity)

mutual
  /-- Enumerate a node or merge the equality variables reached at its root. -/
  def enumerateNode (graph : Graph Symbol Guard) : Nat → List Suspended → Nat →
      EnumerateM Symbol Guard (Fragment Symbol)
    | 0, _, _ => failure .fuelExhausted
    | fuel + 1, scs, node => do
        match graph.node node with
        | .empty => reject
        | view =>
          let here := scs.filter fun sc => EqualityTrie.isTerminal sc.trie
          let below := scs.filter fun sc => !EqualityTrie.isTerminal sc.trie
          match here with
          | [] =>
            match view with
            | .empty => reject
            | .recursive _ => pure (.hole (← allocate (some node)))
            | .alternatives edges => enumerateEdge graph fuel scs (← choose edges)
            | .unresolved _ => failure .unresolvedReference
          | first :: rest =>
            let roots ← here.mapM fun sc => representative (fuel + 1) sc.var
            rest.forM fun sc => unionVariables (fuel + 1) first.var sc.var
            let root ← representative (fuel + 1) first.var
            roots.forM (assimilate graph root)
            mergeNode graph (fuel + 1) root node below
            pure (.hole root)

  /-- Descend edge constraints and retain its residual guard for the caller. -/
  def enumerateEdge (graph : Graph Symbol Guard) : Nat → List Suspended → Edge Symbol Guard →
      EnumerateM Symbol Guard (Fragment Symbol)
    | 0, _, _ => failure .fuelExhausted
    | fuel + 1, scs, edge => do
        require (arityAllows edge.children.length scs)
        let added ← edge.equalities.mapM suspend
        let children ← edge.children.zipIdx |>.mapM fun (node, index) =>
          enumerateNode graph fuel (descendScs index (scs ++ added)) node
        let fragment := Fragment.node edge.symbol children
        match edge.residual with
        | none => pure ()
        | some guard => modify fun state => {state with obligations := (guard, fragment) :: state.obligations}
        pure fragment
