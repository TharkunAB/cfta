# Required and prepared projection: independent proof design review

Reviewed at 2026-10-19 00:43 CEST. Starting commit:
`c6b1c479123f8142064de58d240d4f1b0bdf624a`.
This is a source review. It adds no Lean run, theorem, or proof pair.

The target is sound with the stated physical premises. Keep the false gate
on the original forest. Follow the actual projection and Read on the
prepared forest. Do not transfer the false gate to the prepared forest.

For a nonempty forest path `k :: p`, the useful conclusion is:

```text
exists sourceValue preparedValue sourceRow,
  originals[k]? = some sourceValue
  and prepared[k]? = some preparedValue
  and Route (p.map Int.ofNat) sourceValue sourceRow
  and RowOrigin sourceRow observedRow
  and All₂ Origin sourceRow.children observedRow.children.
```

Retain the literal Project of `preparedValue` from the actual Forest graph.
`RowOrigin` gives full constraint equality, symbol equality, and arity.
It does not give child equality. `Route.mass_lt` gives a strict source mass
bound for each child of `sourceRow`. It gives no such bound for a generated
child of `observedRow`.

The core proof can reuse the existing Safe and Accepted induction.

1. Use the historical false NodeTrace to derive
   `Safe (Route p original) p original`. This step uses the original
   SemanticReady, UnionNormal, and Available facts. The historical trace
   itself suffices; a replay on the prepared value is unnecessary.
2. Define `Lift accept row` by an original row, `accept originalRow`,
   `RowOrigin originalRow row`, and ordered `All₂ Origin` children.
   Prove `Safe accept p original -> Origin original prepared ->
   Safe (Lift accept) p prepared` by path induction.
3. The identity Origin supplies identity child origins. The plain Origin
   supplies Safe.plain. In the ordinary case, `RowMap.indexed` supplies the
   original row. Ordered All₂ recovers the source child at the same signed
   slot. Recurse on the remaining path. A small mutual Origin/RowMap/ChildMap
   lemma transports `Annotated Plain` from original to prepared.
4. Reuse actual Project/ProjectRows induction with this stronger acceptance
   predicate. The union case follows the actual sequential ReadAll calls.
   Canonical row survival retains a selected full row; it does not identify
   reconstructed children with their original children.
5. At forest level, ordered All₂ Origin preserves the forest index. Derive
   that All₂ from the actual Required graph and its exposure domain. A false
   class plus `primary_domain` supplies that domain. One false path alone
   does not certify unrelated Required paths.

The empty remaining path is important. `Project.root` returns the supplied
prepared value. It can return a Mu. The subsequent actual Read can unfold
that Mu. Keep the exact Read and its reader. The lifted Safe invariant puts
every such recursive case in an Annotated Plain region. The existing
`plain_accepted` argument excludes a nonplain observed row using causal
Plain guard support and reader SemanticReady/Available facts. No structural
RowAt for the unfolded row is needed. No observation is rebased to the
unfold result's heap. Reader CostHeap is not needed for this final exclusion;
projection entry CostHeap remains necessary for intermediate effects.

The existing checked retention boundary is an obstruction to a stronger
claim. Its active two-path class has false original primary, successful
Required, prepared ForestClosed endpoints, and true prepared primary.
It rules out false-primary retention even for those closed endpoints.
`Origin.nonplain` is not the missing theorem: it requires a structural RowAt
and does not retain the final ordered child-origin tuple in its conclusion.
The proposed lift handles actual reads instead of adding another RowAt
wrapper.

Source pointers:

- `SourceCurrentPositiveProjectionSourceRoute.lean:40,55,61,154,212,239,298`:
  Route, source mass, Safe, historical gate, Accepted, union and Project cases.
- `SourceCurrentPositiveForestProjectionOrigins.lean:72,113`:
  the existing exact Read and forest-index interfaces.
- `SourceCurrentRequiredRowOrigins.lean:30,68,269,275,353`:
  Origin, indexed full fields and children, actual graph producers, and the
  existing structural nonplain theorem.
- `SourceCurrentRequiredGuardOrigins.lean:27`: the exact RowOrigin fields.
- `SourceCurrentRequiredPrimaryExposure.lean:195`: actual primary domain.
- `SourceCurrentRequiredPrimaryOrigins.lean:29`: actual complete origin
  producer. Its completion proof is not needed if a literal return is given.
- `SourceEqualityProjectionGraph.lean:25,60` and
  `SourceEqualityProjectionRead.lean:18`: actual root, forest, and Read graphs.
- `SourceCurrentRequiredPrimaryRetentionBoundary.lean:139`: the checked
  false-primary retention obstruction.

The statement does not yet transport original scan origins through earlier
native class edits. Its original forest can already be a later phase forest.
It does not prove a generated-output mass bound, a complete outer progress
measure, or Mu publication-to-initial-query ancestry. No new counterexample
or Haskell defect is claimed.

Reviewed source SHA-256 values:

```text
efe04b0a0dfeef6e7dab4f8d3d9b0b3e2436a3380373181ea04cfa4033f9fe28  progress-review-next-step.md
37141d118ba5ebaae46d063873a687d0bb825123d274d43355c0ca9b96fac1d0  SourceCurrentPositiveProjectionSourceRoute.lean
08d9a50d298d7417196ef4147a320f51152444d18b0adea7100faaa8bed8371d  SourceCurrentPositiveForestProjectionOrigins.lean
b06879776627e2fcabc360252ed872be7537db32e3008abda2b48ae0a808f9d2  SourceCurrentRequiredRowOrigins.lean
ced8b8c96614ac5886bdf2046c48412981a17a2740e1dc548523d4951cd1446e  SourceCurrentRequiredGuardOrigins.lean
2e8dd5d596b2f69ae45aa3616710910da1ddb76f0397c3f325643102f80876eb  SourceCurrentRequiredPrimaryExposure.lean
dcc999ee4eda80800d95f8f31abb9e05474485eb6935638ba7db2e9b1793fe88  SourceCurrentRequiredPrimaryOrigins.lean
3e3fd6228c3533d377493266efc40dae2ee73ffa496c4f4ae112e7ee8d195091  SourceCurrentRequiredPrimaryRetentionBoundary.lean
b39e09930df5bd935cded34a7aa3ad17ba467be6d434b071cdd844060a709ccb  SourceEqualityProjectionGraph.lean
f299b66171bdf9452fa2b62b22ddca3371a1fb4916193a57d1fd5ece59f8551d  SourceEqualityProjectionRead.lean
bf8f6847dfc1c8748ef66d31753b8aefbb963d5967e1c772d2937f45024517f0  SourceEqualityAnnotationLanguage.lean
```
