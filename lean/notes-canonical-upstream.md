# Canonical enumeration upstream refresh

Source: `TharkunAB/cfta`, `origin/main` at `c351674e`.
Integration: `79f2e38e`. The former source base was `f201deda`.
The merge preserves the published proof history on `formalize`.
Backup: `backup/formalize-before-canonical-main-20261015-0902`.

## Sized correspondence

Upstream moves `canonicalClasses` from the generator's internal Automaton
module to `Data.CFTA.Interned`. Its complete type and function body are
byte-identical. Sized changes only the import. Its complete implementation
after that import substitution is byte-identical to the previous checkpoint.
The ordinary import uses the same relocated function.

The existing canonical refinement, finite-key transport, reference classes,
solver-decided classes, finite execution, size order, and both distinct-term
rank inverses therefore retain the same source definitions. Optimized Sized
dispatch still returns the reference sequence and complete query result.
The focused build includes SourceClosedSized, SourceSizedFiniteKeysApiLaws,
SourceSizedFiniteKeysDispatchApi, and the recursive reached-check module.
It passes 1,223 jobs. External solver replies, native containers, machine
resources, and lazy heap execution retain their documented boundaries.

## Interned enumeration and synthesis

The UVar enumerator now sorts reachable edges by arity, symbol, canonical
child classes, equalities, and guard. Its class keys include constraints.
It uses the same order for nodes built during enumeration. runsBy applies
a stable descending weight sort after canonical ordering. Weights must not
be NaN. Hectare supplies weights from interned edge identities to retain its
search order. distinctProgramsIn removes repeated programs after typed-term
erasure, and the walk uses it before representative expansion.

These are different sequences from Sized's graph classes. Sized's class
keys omit constraints, and its transition sort retains original tied rows.
No equality between these UVar, program, and Sized sequences is claimed.
The existing generic canonical-class theorems apply to finite closed key
graphs. They do not prove the complete new UVar or synthesis path.

## Preservation and validation

Every older Lean proof, counterexample, and marked draft remains present.
Only audit imports and current notes change. The added and removed lines
of all five retained repair files are identical relative to old and new
main. Stashes and other worktrees remain unchanged.
Preservation records: `/tmp/mcfta-canonical-refresh-preservation.json` and
`/tmp/mcfta-canonical-main-repairs.json`.

All three existing Haskell suites pass in Nix: 293 core examples, 210
generator examples, and 147 refinement examples. All 650 examples pass.
Fourmolu and both active Cabal package formatting checks pass. No local
production test is added. Logs:
`/tmp/mcfta-canonical-main-20261015-tests.log`,
`/tmp/mcfta-canonical-main-20261015-format.log`, and
`/tmp/mcfta-canonical-main-20261015-lean.log`.
