/-- The actual output history retains its full native Post and exact query field. -/
theorem ResourceHistory.native_post
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : EnumerationState.Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (InternedConstructorTemplates.EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
    {next : Option EnumerationState.Next} {output : Output (bits + 2) Typing}
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output) :
    ∃ (returnedInventory : Inventory) (final : Memos),
      Post formulas solver returnedInventory caller output.caller final ∧ final.query = output.queries := by
  induction history with
  | stopped admission => exact ⟨_, _, Post.refl admission.1.context, rfl⟩
  | done admission => exact ⟨_, _, Post.refl admission.1.context, rfl⟩
  | parked _ _ _ _ ih => exact ih
  | ordinary _ _ _ prefixPost _ receipt _ _ _ ih =>
      obtain ⟨_entered, _handle, _scs, _decoded, _edge, _headSeed, _inherited,
        _headInventory, _headCaller, _headMemos, _headBound,
        _original, _entry, _enteredPacket, headPost, _captured, completed⟩ := receipt
      obtain ⟨returnedInventory, final, tailPost, queries⟩ := ih
      exact ⟨returnedInventory, final,
        ((prefixPost.trans headPost).trans completed.post).trans tailPost, queries⟩
