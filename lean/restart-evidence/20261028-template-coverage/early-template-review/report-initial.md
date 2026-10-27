# Structural template assessment

Status: source assessment CLEAR. The semantic draft is UNTESTED. This bundle stays OPEN.

The documented public pruning contract requires the fixed singleton arrow marker at each program application. It also excludes app/4 type constructors while pruning is enabled. Pruning.hs:47-52 and 328-332 state these conditions. Utils.hs:89-102 inserts that marker through mapp. Rewriting.hs:359-365 inserts the same marker in original forbidden templates. Specftacular.hs:1231-1233 and 1281-1306 provide the actual canPrune guard and template selection.

The proposed ProgramEncoding is an independent syntax predicate on complete terms. A constant has one annotation child. An application has four children: annotation, the fixed arrow leaf, function, and argument. Function and argument recursively have ProgramEncoding. An annotation can be any complete term. The predicate does not impose the transformed template or its desired match as an admission condition.

The draft public theorem structuralTemplate_matches takes the actual structuralTemplate original = some early receipt, ProgramEncoding full, and Matches early full. It proves Matches original full. Its proof retains exact symbols, annotation restrictions, child order, both recursive program children, and the original marker choice. It uses Template.Matches directly. It does not use a graph language, a native Packet, future execution, a desired original match, or a final Satisfies premise.

The source structuralProgram helper is private. The direct printed private name cannot parse as an identifier; Root's failed alias probe is preserved. The current draft repeats the private equations as a proof-local helper. proof-helper-comparison.json checks literal equality after the helper name changes. The final change command must check definitional equality at the ACTUAL public structuralTemplate receipt. Successful elaboration is still required. The existing runtime module is unchanged.

The arbitrary malformed-marker witness does not establish a public Haskell defect. Such a term violates the documented fixed-marker admission. It only shows why ProgramEncoding is necessary. No Haskell counterexample was executed. No Haskell changes are proposed.

This local law does not prove that every actual native output satisfies ProgramEncoding. The complete source grammar, the canPrune signature guard, and the original forbidden-template policy still need a public-input correspondence theorem. It also does not prove rewrite decrease, pruning completeness, whole enumeration coverage, termination, or physical Haskell certification. Root owns programs/completion and index-catalog integration. Other workers own partial-match completion and resumed refutation.

The source-index stores nine exact whole inputs and 18 literal cuts. Reviewed scope is listed per input. A whole copy is an identity record; it does not assert that every line was reviewed. Other transitive imports are unreviewed. This worker ran no compiler, native evaluator, build, Git command, network request, or board action. The two retained private-probe receipts were produced by Root.

Draft V1 uses the failed direct private notation and is retained unchanged. Draft V2 uses the proof-local equations and an explicit final definitional change. Neither draft has a successful structural theorem receipt yet. Root will compile the immutable draft.
