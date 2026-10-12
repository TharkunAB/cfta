# Contract formula assembly

`ContractAssembly` follows `Refinement.Guard.contract` through conjunct
flattening, literal-Top removal, free positional-name selection, compact
renumbering, and construction of the ordered `Holds` clauses.

`conjuncts_exact` and `parts_exact` preserve the complete sorted formula
meaning. Only outer `And` nodes are flattened. Other formula constructors
remain intact. Only literal `Top` is removed; no solver result is used.

`named_member` derives exactly the source child-index filter. It uses the
full formula free-name traversal, including quantifier scope and application
heads. The selected indices remain in original argument order and have no
duplicates. Their count is at most the builder's argument count.

`renamingTable` pairs those old names with compact names starting at zero.
Its key and target projections are proved directly. `compact_avoids` derives
that no compact target name captures an unmapped free name. A free contract
name below the builder arity would already have entered the selected list.
This fact closes the apparent conflict when, for example, original arguments
1 and 3 become compact formals 0 and 1.

`renumber_checked` proves that the actual name-only checked substitution
succeeds. `renumber_exact` uses its complete capture-avoiding semantics. The
explicit reverse name table constructs the compact environment.
`compact_value` proves that each compact formal receives the original value
of the corresponding selected child. `contract_formula_exact` composes those
results for every retained conjunct. It does not assume a desired
whole-contract renumbering law.

`clause_target`, `clause_indices`, and `clauses_indices` derive the exact
original child paths in each generated `Holds` atom. `contract_arity` connects
them to the checked source arity gate. `clauses_member` retains the full
pre-conjunction source clause list. The source `allOf` then uses the separately
proved constraint conjunction and canonical guard construction.

The formula theorem describes each conjunct in its own compact environment.
The guard evaluator asks entailment or refutation under the refinements of
that conjunct's named children. It does not assume all unrelated child
refinements. These source query semantics, aliases, and three-valued solver
results remain the existing `SourceContractSemantics`, `SourceHoldsQueries`,
and full guard-evaluation proofs. This theorem does not identify a successful
solver result with arbitrary concrete formula truth.

The input builder's standard arity and argument application come from
`GuardBuilders`. Custom typeclass instances, machine index bounds, physical
formula representations, and the external solver retain their explicit
contracts. No Haskell source changed. The pinned Lean target passes all 98
build jobs.
