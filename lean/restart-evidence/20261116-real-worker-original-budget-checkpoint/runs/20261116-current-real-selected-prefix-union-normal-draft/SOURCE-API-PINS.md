# Source API pins

- SelectedStep.lean:43/99: literal configurable prefix and real narrowing wrapper.
- Action.lean:16: actual prepareWithNarrow. It changes no heap after narrowing.
- OuterNarrow.lean:13: actual Mu/type exemptions and narrowAt branch.
- NativeView.lean:34: actual nodeEdges exposure and filtered makeNode.
- RequiredUnionNormalRead.lean:55: actual exposure preserves union normality, including failed prefixes.
- RequiredUnionNormal.lean:49: actual makeNode preserves union normality.
- PrefixNativeReadback.lean:98: public checked control proof used as the branch template.
- SharedIncomingUnionNormal.lean:32: separate actual SHARED incoming theorem.
- SharedOuterUnionNormalHistory.lean:65/91/97: actual prefix/stopping/literal-construction facts.

The exact source hashes are recorded in SOURCE-PINS.sha256. The prefix theorem has only the past heap invariant as a premise. It does not assume a later UnionNormal endpoint.
