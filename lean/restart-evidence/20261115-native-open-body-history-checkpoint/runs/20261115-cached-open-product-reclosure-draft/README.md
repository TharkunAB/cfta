# Weak ProductShape does not retain witness identity coherence

Status: source audit only. No theorem or countermodel was compiled.

The old ProductShape existential fixes mapped children and complete target keys. It does not constrain each target entry identity. canonicalEdges deduplicates by entry identity and selects the first payload for each identity. A discarded witness row can therefore have a distinct full key and an arbitrary identity which collides with a retained row.

For example, give the mapped arrow row one identity and all four mapped zero-arity var rows a second identity. The four mandatory source alternatives have distinct symbols. The witness still satisfies its mapped-child/full-key equations. canonicalEdges keeps the arrow and only the first var row. The open arrow retains the singleton cutoff free metadata. Availability of the resulting canonical node checks those retained payloads. It does not check the discarded witness handles. This is a structural collision illustration, not a checked full accepted-source execution countermodel.

The current assumptions cannot supply the all-witness residency premise required by stored_open_product_optional_reclosure through the existing canonical-residency API. In particular, canonicalEdges_retains requires all input rows resident. Using it here would be circular.

The exact missing history fact is that one original readback witness is identity-functional: any two witness rows with equal identities are equal as complete values. Every raw product producer already supplies all-products residency, so edge_identity_unique derives this pure finite property. The property can be stored in a stronger value-only result law. The existing weak ProductShape remains unchanged.

With that finite property, canonicalEdges_ids selects a retained representative with the same identity as each witness row. Functionality identifies the representative with that row. Available plus Facts.Linked then gives all-witness residency. The existing reclosure theorem applies without changes.

The requested reclosure theorem from OLD ProductShape alone remains OPEN in this packet. The packet does not add an assumed identity condition to the full accepted-source target. Root assigned a separate stronger result predicate and genuine history producer to retain the condition from actual raw results.

No compiler, live source, Git, board, Haskell, or /tmp operation was used. This finding concerns the formal result predicate. It is not a reported Haskell bug.
