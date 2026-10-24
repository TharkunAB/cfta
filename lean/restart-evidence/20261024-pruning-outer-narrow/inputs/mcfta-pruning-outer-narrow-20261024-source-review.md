# Outer narrowing source/API review

Status: SOURCE_API_CLEAR; exact frozen declaration review remains pending.

Reviewed on 2026-10-24 at 07:14 CEST. Arity authored the immutable plan. I reviewed its source/API correspondence. I did not author a mathematical body or run a compiler, prepared program, Git command, network operation or board operation. All writes for this review are outside the repository.

The actual source at Pruning.hs127–132 matches the proposed order: Mu returns the complete original node; every other constructor checks the ORIGINAL raw UVar in the incoming types set; the fallback calls narrowAt with holeKey of the same incoming typing and raw ID. It does not use the representative, updatedTypes or a replacement typing. Metadata already has pending, types, openHoles and typing. The wrapper needs no new metadata or callback framework.

Native matchMu accepts only InternedMu. InternedUnion is a distinct constructor. recursiveBoundary accepts both and would implement the wrong branch. A non-type union must use the repaired native reader in the fallback. Empty and reference inputs follow the same literal branches. Availability and closedness restrict the finite producer, not the executable definition or all-fuel branch equations.

The bypasses return the exact input heap and complete input value. Their branch expressions must contain no holeKey or narrowAt invocation. The raw-membership equation is valid for every Value constructor, including Mu; its proof may inspect constructors while the executable definition still inspects Mu first. No sortedness or uniqueness premise is needed for List Nat membership. Native IntSet extraction remains separate.

The current narrowAt_complete API derives a single completed run from Ready, Available and free=[]; it returns actual output, actual final heap, Keeps, output availability/closedness and retention at the chosen fuel plus every extra. The combined producer can use pure_keeps on both bypasses and this API once in the fallback. It must not conclude Ordinary for a Mu bypass or assume a final Ready/Keeps certificate. An equal result handle after fallback does not prove heap equality. The no-effect bypass statement is about the modeled heap operation, not runtime allocation, timing or native memo behavior.

The source public prunedPrograms function already takes holeKey, fits and admits. Reusing those exact parameters proves its literal operation; it does not prove semantic pruning. The concrete phase4 caller uses PartialTyping, canonicalVariables(holeTypeOf typing rawID), constantFits and flip typeAdmits. Those typing/unification/key and predicate semantics remain separate. SourceTypingRules is a bounded rule-row model and does not supply this concrete PartialTyping representation. The fixed full Symbol alias must remain unchanged; neither the refined label nor independent NativeGuard may be replaced by String or EnumGuard.

For later enumeration coupling, derive the classified old value from the actual observed slot first. Preserve expand-entry E on a bypass; earlier reads and false repetition checks may have compressed the forest. Do not run the fallback merely to discover the bypass value. Only the actual fallback can consume narrow_pending_complete, with lookup functionality identifying its derived old value. Empty rejection, changed-branch reread Q/write F and raw-ID versus root roles stay separate. EnumerationUntil currently accepts a pure handle function and has no native heap/result carrier. No driver integration, maintained-index correspondence, native Int bound, typing monotonicity, pruning soundness or H6 strengthening follows here.

The proposed definition, three all-fuel equations and finite producer fit the stated70–115-line estimate and proposed hard140 cap by direct API composition. Exact line budget and all scoped inventories still require the separately frozen declaration gate. No body or compiler authorization follows from this source review.

## Inputs and read scope

The table records full-file identities and the actual source cuts read for this review. Hashing the full files is programmatic. It is not a claim to have manually read every large Haskell file or re-proved its foundations. The proposal had no pins/FROZEN controls when inspected at07:14; it was not treated as an authoritative declaration snapshot.

| Input | Read scope | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `/tmp/mcfta-pruning-outer-narrow-20261024-plan.md` | whole68-line plan | 12212 | `434c9435bb7248ecd5142d26b7df4de25d2b0bcbf5c02ac7389f80fcb7759bf9` |
| `/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Pruning.hs` | 85–141 | 16989 | `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` |
| `/home/tritlo/Code/mcfta/specftacular/src/Specftacular.hs` | 1099–1119 | 77825 | `b5a19e8c83908ff2de3cf3ee704731733224d96f36b7fb597afcd0fa017dbace` |
| `/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Types.hs` | 800–817 and975–1012 | 57422 | `e559f049d1f1c4397606e36580322ae5d3f256f1601a8d481ec25a1f4e429119` |
| `/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Utils.hs` | 225–248 | 9246 | `2737df7df4bce7178e45c96db3bf550a0ce4c2d7d57ed131e2689071ec2e53ec` |
| `/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Type.hs` | 270–300,355–372,600–615,665–680,760–788 | 36883 | `f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningRecordTypes.lean` | 1–150 | 13138 | `c5a714825eab5f8efa89eaecbc5cae7438136834010d4270257d145af108bfbf` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningNativeView.lean` | 1–90 and140–177; unchanged earlier complete source review | 10881 | `0cf2d0d30d1a231dd6a1c53dc8a78bc0b8c37972ff5fe3d55b2767e9f6f98571` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceEqualityRequiredCache.lean` | whole105-line source | 6081 | `7cfdad372cba5716c4dc32a7097af8060a27e903fe334f89a2062757b664a733` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningTemplates.lean` | 1–24 | 8380 | `1890878e308ec4debe67d6e74755bc00d93898f59a3a4ed1e5fa188c02899156` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationUntil.lean` | 84–128 | 8864 | `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceTypingRules.lean` | 1–42 | 7561 | `883358821462c869be1ed01b284c674b62d5fa6519495661cd89e4bcb305fdc1` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/MergedSourceComparison.lean` | 1–90 | 5587 | `215330f70fa1b4ad03924607a653c5ebce213f866f2cc1f588a3b25ce25132fc` |
