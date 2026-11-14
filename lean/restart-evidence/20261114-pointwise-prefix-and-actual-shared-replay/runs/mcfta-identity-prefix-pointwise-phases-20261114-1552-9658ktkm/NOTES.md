# Actual supported identity-prefix phase fields

Status: UNCOMPILED proof candidate. Root owns Lean validation and publication.

Apply candidate.patch to SourcePruningEnumerationObservedPrefixFuel.lean.
The candidate adds one IdentityPrefixCheckpoint import and two proof declarations.
Removing those additions recovers every byte of the original file.
Every old header, proof and operational definition remains unchanged.
The new import graph is acyclic. No standalone namespace overlay is used.

The main target is
`MicroCFTA.SourcePruningEnumerationSharedRecursive.prefix_identity_phase_resources_at_any_budget`.
Its initial parameters are exactly those of the checked prefix_identity_resources_at_any_budget.
Its actual operation uses Unit metadata, identity narrowing, templates [], no stop, no order,
and the same supplied fuel for all six prefix budgets. It does not vary recursive depth.
The initial Packet, allocation Fits, annotation Heap and actual selection receipt are explicit.
No future phase, result, callback or resource provider is an input.

At the actual supplied common bound, each supported observation has one exact phase:
- Parked: exact checked core, cached endpoint and restart raw observation; Ready; IncomingAvoid;
  suspended mass at most the original mass; CurrentPrefixResources for that same observation.
- Empty fresh: exact reject preparation and empty action observation; Ready; IncomingAvoid;
  exact original checked-core mass; CurrentPrefixResources for that same observation.
- Nonempty fresh: exact preparation, caller advance, query bundle, singleton pure action,
  cached endpoint and singleton Right observation; Ready; stored original handle/bucket;
  IncomingAvoid; original bucket length at most original suspended mass; exact original mass;
  CurrentPrefixResources for that same observation.

The producer identity_checkpoint_resources supplies every original phase/resource field.
Its lower producer runPrefix_identity_selected_complete also supplies Ready and IncomingAvoid
for both repeated and fresh checks. The candidate retains those fields for parked and empty phases.
For a false check, checkRepeated_false_frame and the actual read frame give exact checked-core mass.
The same lower producer's check receipt supplies the Success proof used by that frame law.
No semantic existence, repeated-clear satisfaction, or finite productivity premise is inferred.

The proof compares three actual observations at one common larger bound:
- the small supported observation replayed from fuel to fuel + (checkpointBound + receiptFuel);
- the checkpoint producer at checkpointBound + (receiptFuel + fuel);
- the original read/check producer at receiptFuel + (checkpointBound + fuel).
The arithmetic shifts make these budgets equal.
Private prefix_identity_supported_moreFuel retains the complete supported prefix result.
That equality transports the exact phase witnesses and resources to the supplied small bound.
The lower producer's exact phase equation identifies the same checked core and admission fields.

The phase theorem preserves stopped, missing parked-adapter, and failed-native branches explicitly.
Those branches have no phase-resource assertion in that theorem.
The companion public law
`SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.unsupported_or_failed_prefix_stops`
proves the actual positive-depth worker consumes each unsupported observation with local outputs [].
For a failed preparation, its premise uses the exact none/none/none/none continuation shape emitted
by runPrefixWithNarrow's failed branch. It retains the reached caller and saved queries.
Stopped and missing-adapter observations retain the original caller and queries.
The exact stopped reason contains the same observed prefix.
The shape is a current operational receipt, not a future phase premise.
The theorem has an arbitrary actual child operation and keeps recursiveFuel fixed.
It never invokes that child in the covered local cases.

Static checks compare the initial header and every checkpoint field with their existing producers.
They also verify that no old source byte changed and that no bypass token was added.
No compiler, Lake, Nix, heavy job, Git, board, live write or subagent was used.
This packet has no Lean elaboration or axiom-closure credit until Root checks it.

Scope stays open: later scan/callback stops may retain already emitted outputs.
This local empty-output law does not prove their inclusion in a larger successful worker result.
The full every-budget partial-output history remains separate.
One finite accepted common original-root term and assignment, parked backward completion,
and the original typing, LPO, language, stream, count, weight, rank and compiled-Haskell scope stay open.
