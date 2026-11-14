# Worker proof repairs

Status: UNCOMPILED. Root must compile this source.

The candidate preserves both approved theorem headers. It changes only three parts of the resume proof. The final entry proof, all maps and actual workers, and both axiom print commands remain exact.

The first diagnostic leaves equal-looking empty output maps with different source metadata types. `List.map_nil` reduces both maps to the same empty list.

The accepted Right branch retains an unreduced match on a fully known narrowed prefix. `dsimp only` exposes that branch before applying the existing local preparation equality.

The unsupported multiple-row branch still contains Boolean tests inside opaque successful row payloads. The repair destructures each actual successful payload and splits its actual Boolean. It then reduces the prefix match before applying the existing selected-failure equality. It preserves all rows and their order. It adds no condition on a payload or result.

All complete and stopped observations remain in scope. No theorem hypothesis, definition, datatype, operational worker, hook, provider, selection contract, adequacy condition, or proof hole was added.

The exact input SHA matches Root's private worker check1. The two headers match byte for byte. The final entry theorem and instrumentation match byte for byte. Each text edit has an exact inverse. GNU patch applies and reverses with zero fuzz and exact byte checks. The source pins and compact actual diagnostic excerpts are included. No compiler, live source, Git, Haskell, or board operation ran. The failed check and all older packets remain unchanged.
