# Concrete enumeration constraint projection: source review

Review cut: 2026-10-24 09:56 CEST. Status: SOURCE SEMANTICS CLEAR, SUBJECT TO THE BOUNDARIES BELOW. This is a review of the proposed semantics. The exact declaration owner was not frozen at this cut and requires a separate review. I authored no definition or proof.

The proposed projection supplies the missing concrete equality/residual split. It must use the actual `SourceCompactGuards.sourceEqualities constraint`, retain its class order, and read those classes through the existing `EnumerationEquality.readClasses`. For a syntactically positive guard, no residual is needed. Otherwise the residual must retain the ENTIRE original constraint. This matches native `Constraint.equalities` and `Constraint.residual` (`Constraint.hs:130–177`) and the residual insertion in `enumerateEdgeWith` (`Enumeration.hs:765–773`). It must not retain only `constraint.guard`: the source stores the complete `edgeConstraint` with the actual fragment.

The complete semantic law is feasible from existing APIs. `SourceEqualityGuardReadback.source_cached` derives the normalized output invariant from the genuine stored equality-cache invariant. For every returned class it provides nontriviality, absence of prefix contradiction, and canonicality. `EqualityNormalize.consistent_supported` applies to `paths.eraseDups`; `EqualityTrie.toPathTrie_correct` then derives actual trie-construction success, validity and path membership. `EnumerationEquality.trie_pcs_exact` converts that exact path membership and nontriviality to the enumerator’s common-existing-subtree predicate. These facts derive the equality conjunction. They must not be assumptions that the projection or callback already has the desired meaning.

At a positive guard, `SourceEqualityPCSGuard.positive_source` identifies complete constraint acceptance with satisfaction of the actual source equality accessor. At a nonpositive guard, the residual is the complete constraint itself. `SourceEqualityPCSGuard.own_sat` supplies the extra equality conjunction from acceptance; the reverse implication follows from the retained residual. Thus the requested equivalence to all `EqualityHolds` conjuncts and the concrete `ResidualHolds` predicate has the required two directions. The formulas and solver are the parameters of the existing concrete guard evaluator. This does not assume arbitrary callback congruence or external solver correctness.

Important branch distinctions:

- `Top`, distinct-path `Same`, and conjunctions containing only positive operands may omit the residual. Source normalization can still detect a prefix contradiction in such a conjunction.
- Reflexive `Same p p` deliberately fails the positive syntax test. It asserts that path `p` exists; dropping it as a trivial equality would accept missing paths. Retaining the complete constraint as residual is correct, including when `p` is nonempty.
- Negation, disjunction, scoped substitutions, refinement predicates and other nonpositive guards retain the residual. Failure of positive extraction is not projection absence: the native accessor retains the stored equality payload in this branch.
- Projection absence means the actual source equality accessor is contradictory. It does not mean every unsatisfiable complete constraint, nor an unsupported guard. For example, a stored empty class list with guard `Bottom` still has a present projection with a false residual; native interning separately rejects a contradictory edge.
- Native `unsafeGetEclasses EqContradiction` raises an error (`Equality/Constraint.hs:316–319`). The proposed Option is a checked counterpart of this precondition. A later edge action must handle absence explicitly and retain the real constructor/interning invariant that prevents the unsafe native call. It must not describe the native function as returning an ordinary empty class list.
- `readClasses` is total because `classTrie` uses `getD .empty`. On arbitrary malformed raw classes that fallback can discard information. The stored `Cached` premise and the derived construction-success proof must rule it out for the public correctness result. A mere active/nontrivial-class premise is insufficient to prove valid tries; consistency is also needed.

This closes a CONSTRAINT-MEANING prerequisite, not the complete per-edge enumeration action. Child-position arity checks, allocation and ordering of equality UVars, descent into suspended buckets, terminal child merging, actual final heap/state effects, residual-obligation insertion, and default canonical edge selection remain separate. No Graph equality or child-output law is needed for this projection.

There is also a computability boundary. `sourceEqualities`, its staged normalization dependencies, and `SourceEqualityPCSGuard.holds` are declared `noncomputable` in the installed model. A direct definition through those APIs must respect that fact. It is a concrete mathematical projection of the source representation, but this review does not certify compiled native extraction or a runnable Lean implementation. If execution is required, select a computable normalization implementation and prove its equality separately; do not silently replace the actual accessor with raw classes.

The existing path domain is `List Nat`. The theorem can range over all formula types and all modeled finite terms, subject to the explicit cached-source and decidable-formula requirements of the chosen header. It does not cover negative or overflowing native `Int` paths, native container extraction, Formula/Text interning, or refinement solver soundness. Full labels and the complete constraint must remain intact. The full goal remains ACTIVE.

I read the bounded source locations below and checked complete input identities. I ran no compiler, selected program, import, parser, native probe, Git, network or board operation, and changed no repository file.

| Input, relative to `/home/tritlo/Code/mcfta` | Reviewed locations | Bytes | SHA-256 |
|---|---|---:|---|
| `cfta/src/Data/CFTA/Constraint.hs` | 119–177 | 14831 | `dee73d12be74af16c54f1c6856a3a60b1c1ae612ad8a15d1665210e2c63641f3` |
| `cfta/src/Data/CFTA/Equality/Constraint.hs` | 122–143, 265–278, 316–319 | 21706 | `9dd1a13bd4422a0778bee419679f34e45901ec1d38442a46781df84952537c48` |
| `cfta/src/Data/CFTA/Enumeration.hs` | 756–775 | 71269 | `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` |
| `lean/MicroCFTA/SourceCompactGuards.lean` | 18–29, 430–501, 516–538 | 32004 | `f325f71a99c33a2d966cd5a8caebb2924d91b0df612936e0e86d9c8aba5b4d60` |
| `lean/MicroCFTA/SourceEqualityGuardReadback.lean` | 15–61, 85–96 | 5802 | `8ffa379cf0da81b54e9a6bff4941110b57fb9d775f4a44aac8a73364d8c5c7df` |
| `lean/MicroCFTA/SourceEqualityPCSGuard.lean` | 39–98 | 6228 | `80a9ed35efe9992207429c7d45be0282c9484368834bcb36a42a4c8bb72857b4` |
| `lean/MicroCFTA/EnumerationEquality.lean` | 17–48 | 10033 | `7b01bbaa5223bec8498197b3dbf4b1b8071c729b457043f650eb235f502556cd` |
| `lean/MicroCFTA/EqualityNormalize.lean` | 30–46, 738–779 | 76459 | `e3f1441385493c750051466cd8cb24b88a4f33a6c9b285932360a43963aada3d` |
| `lean/MicroCFTA/EqualityTrie.lean` | 57–72, 464–473 | 44327 | `0cf7d0b98a7bbc24382fde259b3f9b71462c752c347ad6e7788b9e95b41e10d5` |
| `lean/MicroCFTA/EnumerationCorrectness.lean` | 84–92 | 76898 | `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d` |
