- **Recursive field-pool invariant: confirmed, unfixed.** Current main
  `999c04a5` accepts a field-specific pool for a field of the root datatype.
  The path was added in `d0966953`. With `data Chain = End Bool | Next Chain`,
  require `End True` at each Chain node and give Next's child the pool
  `[End False]`. `deriveLTAFrom @Chain 0` succeeds and enumerates
  `[End True, Next (End False)]`. The latter violates the independent
  all-node invariant, but `holds` returns `True`. The reproducer uses a
  lawful nonnegative `Literal Chain` encoding.
  Affected code is `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs`
  (`fieldAtoms` and `evaluate`) and
  `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive/Internal.hs`
  (`derivation` and `alternativeGenerator`). Field-pool generation bypasses
  recursive derivation; value evaluation returns `below=True` for that field.
  Run `nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=cfta -package=cfta-generator lean/restart-evidence/20261016-frontend-node-view-refresh/derive-self-field-draft.hs'`.
  The successful terminal-zero output is in `derive-self-field-retry.log`
  in the same directory. The frozen file retains its historical draft comment;
  it was subsequently executed. This focused counterexample passes as a
  program; all 791 existing examples still pass.
  No repair commit or local patch exists. The advertised each-node contract
  and opaque supplied-subtree interpretation give different languages.
  Settle that contract before a behavior repair. The old type-wide atom also
  makes `holds` skip descendants, but the high-level derivation then rejects
  the root annotations as `UnknownConstructors`. The new field-local case
  keeps the root derived and succeeds. Do not conflate those two cases.
