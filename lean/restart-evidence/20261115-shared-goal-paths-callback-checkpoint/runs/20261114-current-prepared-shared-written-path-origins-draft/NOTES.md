# Prepared shared write: raw path sources

Status: UNCOMPILED candidate. No compiler or live source change was made.

The public candidate is
`MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.prepared_terminal_child_written_path_origins`.

The theorem consumes an actual `CachedOwn.prepare` singleton, an exact
`staged[position]?` selection, and an actual successful shared terminal child
dispatch. It derives the projection internally. It does not take a projected
trie list, an incoming call, an older bucket, or a model as a premise.

The result retains the actual terminal partition, prefix, shared fold, and
shared incoming call. The incoming receipt supplies the canonical target,
the exact older stored bucket, the compression read, the written Core, and
the actual ancestry update.

The exact ordered written list is:

```
nonterminal (descend position parentBucket)
++ nonterminal (descend position (suspendedVars captured.counter tries))
++ oldScs
```

Each occurrence in that written list has one of three sources:

- An indexed original parent suspension. Its raw variable is unchanged.
  Its represented source path is `position :: writtenPath`.
- An indexed own trie from the actual projection. Its raw variable is
  exactly `captured.counter + ownPosition`. Its represented source path is
  `position :: writtenPath`.
- An indexed occurrence in the actual older stored bucket. The complete
  suspension is unchanged.

The list equality retains order and duplicate occurrences. The theorem
quantifies over every written occurrence by `getElem?`. It uses no recursion
key comparison and derives no target equality from equal trie shapes.

The proof reuses these public producers:

- `SourcePruningEnumerationCachedOwn.prepare_inputs`.
- `SourcePruningEnumerationPathTransport.descended_path_original`.
- `ChildDispatch.terminal_singleton_raw_target_incidence`.
- `SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history`.

Two private helpers retain the raw variable during one descent and identify
the exact own allocation index. The descent helper uses the public path
producer. It needs no trie validity premise. The own helper proves an
allocation identifier equation. It does not claim global disjointness or
fresh root validity for an arbitrary malformed input state.

The captured preparation state and the actual child input state are separate.
Earlier siblings can change the native caller and the child input state.
No equality between those endpoints is assumed or derived. The exact staged
selection links the static child bucket to this particular preparation.

This is one concrete operation in the required history. It does not extract
the complete sequence from an emitted root. It does not identify the parent
bucket with an earlier `Entry` bucket. It does not retain written obligations
after a later recursive clear. It does not construct a satisfying assignment
or prove finite productivity. Those remain separate proof obligations.

The original full target remains open: every actual emitted partial root
must have ONE finite accepted completion of the SAME original root under ONE
compatible assignment. That assignment must satisfy retained domains,
paths, aliases, residual guards, and all historically removed obligations.
The target includes actual stopped output prefixes and the current shared
worker. No smaller target replaces it.

The exact target remains in:

`lean/restart-evidence/20261114-shared-child-resources-and-atom-steps/runs/mcfta-same-branch-clear-causal-review-20261114-1659/RELATION-TARGET.md`

`lean/restart-evidence/20261114-shared-child-resources-and-atom-steps/runs/mcfta-same-branch-clear-causal-review-20261114-1659/EXISTING-SAME-SOURCE-INITIALIZER-HEADER.lean.txt`

No Haskell defect or change was established. No live Lean source, Git state,
board, compiler state, or temporary evidence was changed.
