# Nested scope environment correspondence

`SourceScopeEnvironment.lean` proves simultaneous and nested scope transport.
`environment_cons` exposes the exact source identity-removal rule. The main
proof retains repeated formal names; it does not assume that a scope is a
map with unique keys.

`environment_commutes` proves one simultaneous scope preserves a finite
name relation. Each formal and actual name must belong to the tracked set.
The fresh map must fix formal names and be injective on tracked names.
These local conditions ensure that both sides remove the same identity
entries and select the same first remaining formal occurrence.

`aligned_replacements` obtains the exact replacement lists from the source
resolved-record relation. `scopes_commute` then proves the full reverse-order
environment fold. `scoped_formula_equivalent` connects the fold to the
repaired formula substitution semantics for original formulas whose free
names are fixed by the fresh map.

`injective_live` derives finite injectivity from unique target names and
avoidance of unmapped tracked names. `lift_related` constructs the initial
environment relation from the reverse table in FreshEnvironment. These two
conditions are not assumed as unexplained whole-scope properties.

The remaining source instantiation must track the semantic ambient names
and source-generated contract names, then prove scope closure in that set.
The full used-name set is too large for this purpose: it also contains
constructor names at refinement-only positions. Those names can differ
between grouped terms and are not part of the formula's semantic environment.
Sorted declaration-domain transport remains separate.

Validation: `lake build MicroCFTA.SourceScopeEnvironment` succeeds with the
pinned toolchain. There are no proof placeholders or new axioms.
