# Constrained grammar construction

`MicroCFTA/Construction.lean` formalizes the requested source-language to FTA
boundary. A grammar has named nonterminals, finite production lists, nested
constructor patterns, and a semantic constraint at each constructor. Each
production consumes one constructor before it can refer to a nonterminal.
References can be cyclic.

`Derives` is an independent finite derivation judgment. A reference selects a
production. A constructor matches the ordered child patterns and checks the
constraint on its complete tree. This definition does not mention an FTA.

`compile` emits one edge per named production. It also emits one edge for
each nested constructor state. It places each constraint's decision procedure
in the edge guard. It does not enumerate terms or require an acyclic grammar.

The checked results are:

- `compile_exact`: the compiled FTA accepts all and only the grammar's finite terms.
- `compiled_enumeration_exact`: enumeration is sound and complete at its stated height bound.
- `derives_iff_eventually_enumerated`: every valid finite term occurs at some finite bound.
- `compiled_states_closed`: a finite complete list of nonterminal names gives an
  explicit finite state list closed under all compiled transitions.
- `Constraint.test_correct`: converting a decidable semantic constraint to a
  Boolean edge guard preserves it exactly.

The constraint constructors include path equality, conjunction, disjunction,
and negation. Equality requires both paths to exist. Ground liquid formulas
use `CoreFormula.evalFormula` and a supplied integer interpretation of a
complete term. `Constraint.simplify_groundFormula` proves that core formula
simplification preserves these constraints.

Three checked examples exercise different boundaries. `unaryGrammar_complete`
and `unaryGrammar_enumerates` include every finite number of successors through
a cyclic reference. `equalPairGrammar_enumeration` yields exactly the two equal
pairs from two leaf alternatives. `nonnegativeGrammar_enumeration` rejects a
negative integer alternative and retains zero and one.

This is a concrete reference compiler for the declared language. It is not an
extraction of the Haskell generator builder, interner, or refinement compiler.
The source libraries provide the corresponding node, edge, child, and guard
operations. Their additional caches, observation partitions, solver calls,
size accounting, and sampling rules need their own correspondence proofs.
The separate model modules cover those boundaries to their stated extent.

The decidable-constraint parameter is a real condition. Ground formula
evaluation supplies one total procedure. This result does not assert that an
SMT solver always decides arbitrary liquid entailments. An unknown solver
verdict cannot establish either exact acceptance or exact rejection. The
source's unsupported and unknown branches remain part of its API contract.

The construction theorem composes with `Language` optimizations and the
`DistinctRank` reference index. It does not by itself establish an efficient
ranking implementation. The source `Symbolic` count and selection operations
are covered separately in [notes-symbolic.md](notes-symbolic.md).
