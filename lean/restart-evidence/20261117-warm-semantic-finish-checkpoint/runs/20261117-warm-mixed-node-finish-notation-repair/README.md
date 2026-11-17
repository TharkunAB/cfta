# Mixed warm finish: duplicate notation repair

Status: FROZEN UNCOMPILED. The original bb7be9b2 candidate and failed check 7599 remain immutable. This new packet has no compiler or theorem credit.

The repair removes exactly 28 nested local notation declarations that duplicate the five local aliases in the outer namespace. It keeps the outer declarations and both distinct local Guard notations. The opened SourceSynthesisGeneralizeSyntax.Guard at line 21 is an abbreviation of the same Constraint type. No new notation, import, declaration, proof step, limit or linter setting is added.

The original public complete header 8e54713dbc4156556693a2236e0e4bb2b4f2f3e29ba81b4772456a887fc4cc1c and all six private semantic headers f72477300070b8411ea3884858be4bceecf9820d8aa6b4f10bf2052f3e37ece7 remain byte-exact. Each private semantic theorem and its complete proof suffix match the original. The entire public theorem and proof suffix match the original. The public and optional private probes are unchanged. COMPARISON.json and EXACT-DIFF.patch record these checks.

The first observed ambiguity is at original line 99. The nested Ordinary namespace inherits the outer aliases and redeclares them. The failure log then reaches the original maxErrors limit. Later diagnostics include cascades from those unresolved types. This packet makes no speculative semantic proof changes. Root must recheck the remaining proof after the notation ambiguity is removed.

SOURCE-PINS records the current normal input hashes. HISTORICAL-SOURCE-PINS preserves the original candidate's input hashes. The only historical owner changes are the checked warm reader EOF exports reported by Root. FAILURE-PINS pins the original failed log and exact compiled source. The original source and evidence files are not edited.

Root should replace only the Mixed candidate with SourceCurrentNativeWarmMixedFinish.lean in the existing six-module check. All definitions, C, Edge, Gamma, af8 and public/private probe fixtures retain their original input bytes. The expected public report count is unchanged. The same-file private fixture still has seven optional reports. Default 200000 limits, full fixed H, authentic entry, original source/resources/fuels, all ordered cases and the exact auxiliary-prefix derivation remain unchanged.

The original full warm C/M history and actual child pair-absence chain are unverified until their complete checks exit zero. This syntax repair supplies no native compatibility, inhabitance, Type/Marker truth, guard truth or full finite-completion claim.
