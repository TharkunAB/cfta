# Initial-resource root integration review

The reviewed final root source is `SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot.lean`.
Its SHA-256 is `d0a3c512af4466990c32e867ef3a58c8bf5765ae22d78f4733f540a0eeb7673d`.
No material defect was found.

`constructed_root` at line 90 takes original source syntax, finite-ordinary syntax membership, actual covered field history, initial cache validity, formulas and solver, a fixed conjunction budget, and initial constructor headroom.
The headroom at lines 98–99 depends only on the independently constructed original value and heap.
Its node and edge budgets compute the original row, arity, hereditary guard, and height envelopes at lines 34–43.
It takes no outer worker success, completed outer graph, reached-entry Plan, final result profile, or desired body law.
The constructor success in the headroom antecedent is the independent original source build. It is not outer reduction success.

The original build derives its own finite-ordinary value and admission at line 114.
Cold-table certificates and the initial active-owner bound are derived at lines 115–120.
The initial inherited value is the actual canonical empty allocation. The proof does not assume its identity is zero.
The root invokes the new strong rank induction at lines 121–129.
The returned NodeLaw yields full language equality through the empty inherited payload at lines 131–133.

`prepared_root` at line 136 derives its field history with literal `prepare_complete` before it calls the same root theorem.
It preserves the exact preparation cache and fields through the preparation receipt.
It requires normalized cached source equality fields. It does not require those fields to be preloaded at the final cache.
Both endpoints return the same actual graph, strict Reads, Checks, full Post, resident result, quantitative causal stores, narrowing, universal output certificate, constructor Work, final fitting supplies, and full language equality.
The stable literal worker return uses the same complete caller state and fixed conjunction budget.

## Domain and remaining scope

The source domain is exactly the `FiniteOrdinaryConstruction.Node` domain used by the earlier `FiniteOrdinaryOuterRoot` constrained root.
The new theorem replaces that older root's reached-entry Plan premise with conservative initial constructor headroom.
It does not weaken the finite-ordinary source restriction or silently use the older Plan.
Finite ordinary excludes Mu and explicit unions. Closed source construction does not introduce runtime references.
Full guards and nonempty equality classes are allowed, subject to the actual source-field preparation contract.
The older PlainRegion theorem has a different domain and permits some opaque terminal constructors. It is not a claim about this new domain.

A universal numeric Plan over arbitrary raw Reach remains a separate theorem.
The current root constructs its own finite execution by rank induction and carries its remaining headroom through actual prefixes.
This does not prove general constrained Mu termination, arbitrary warm initial tables without their causal certificates, whole-library Haskell correspondence, or a GHC allocation schedule.
Headroom counts constructor supply. The theorem does not provide a bound on instruction count or elapsed time.

## Independent executable proof checks

`initial-root-kernels.lean` imports the canonical root module with every linter enabled.
It also enables explicit proofs, universes, deep terms, full names, and one million print steps.
Final run `initial-root-kernels-6.log`, process 49373, exited 0 with no warnings or errors.
It prints six axiom/full-signature pairs: one result definition and five integration theorems.
The final log has no sorryAx, omitted terms, or truncation.
The used axioms are the standard propext, Classical.choice, and Quot.sound.
Earlier failed drafts and the intermediate successful draft with one unused simp warning are preserved.

The integration theorems establish:

1. `constructed_then_warm` constructs the original root execution from initial inputs. It retains StableRun, the same actual graph/Reads/Checks/Post, quantitative stores, narrowing, universal certificates, full language equality, and constructor Work. It derives both final supply inequalities from that same Work trace.
2. The first theorem also derives the completed root's exact ready cell from its actual first-owner protocol and frame. The literal repeated node call succeeds with all ten bounds zero and returns the identical complete caller state. Its Work is zero. This is stronger than requiring renewed headroom for the same ready hit.
3. `prepared_fields_and_root` constructs field history and all actual final field loads/readbacks. It composes that history with the same initial-only root and warm-repeat proof.
4. `prepared_endpoint_supplies` directly exercises the new production `prepared_root`. It retains its exact actual Reads, full Post, universal certificate, language equality, Work, and both final supply bounds.
5. `guarded_nullary_budget_zero` instantiates an actual nonempty ordinary syntax row with an arbitrary cached full guard at fixed conjunction budget zero.
6. `guarded_nested_budget_zero` instantiates nested ordinary syntax with two arbitrary cached full guards at conjunction budget zero. No completed child execution or future profile is supplied.

Reproduction from the repository root:

```
env LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -D linter.all=true lean/restart-evidence/20261016-outer-initial-headroom/initial-root-kernels.lean
```

No production source was edited for these integration checks. No Lake, Git, Haskell, or host execution was run by this review.
