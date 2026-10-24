# Source-only V2 metadata repair

V2 removes three pseudo-binders created from the expressions `first :: rest`. It repairs the missing final parenthesis in the pending premise type. The scope count changes from272 to269. The insertion map points to V2. All31 compiled literal fragments, public propositions, instance headers, local types, source snapshots, cuts and import identities stay byte-identical.

V1 and its controls remain unchanged. V2 retains the exact V1 controls as provenance. Guard and Root found the issue during static owner review before body authorization. No Lean failure, proof/body change or compiler execution occurred.
