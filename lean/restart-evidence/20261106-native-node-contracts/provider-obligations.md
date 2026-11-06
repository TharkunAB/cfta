# Native node provider obligations

The existing Graph node view preserves the outer recursive case before expansion.
Candidate selection, repeated-recursion handling, and ancestry tracking use that case.
A provider that maps every flattened edge list to alternatives loses this distinction.
No refinement for that mapping is proved.

The actual provider must first classify the outer native node. A recursive model body
key must correspond to one native outer unfolding. Ordinary alternatives must reproduce
the actual edge sequence. The source operation nodeEdges remains a payload candidate
after classification. It is not an established complete provider.

The received Operations source has these distinct cases:

- Ordinary nodes select the stored edge list.
- Empty and direct Rec inputs select an empty list.
- A Mu whose one-step unfolding is ordinary selects that stored edge list.
- The fallback traverses recursive and union members with an identity worklist.
- A Rec in that worklist selects an explicit error.
- The fallback converts its accumulated result through Set.fromList and Set.toList.

The model must preserve the direct and fallback ordering and duplicate behavior.
Language-set equality alone does not establish counts, order, or rank.
Identity stability and memo behavior require actual laws.
Errors cannot all become model emptiness. Derive their unreachability from actual
construction and both workers, or account for implementation behavior. Add no supplied
validity or closure premise to the final worker theorem.

The received Mu term pattern delegates matching to matchMu and construction to createMu.
The local unfolding step applies the matcher's returned function to the same input node.
The actual matchMu owner, complete command, and contract remain unknown.
The pattern alone establishes no substitution or finite-closure law.

No worker-reachable counterexample or required Haskell repair is established.
No new mathematical theorem or runtime refinement is claimed.
