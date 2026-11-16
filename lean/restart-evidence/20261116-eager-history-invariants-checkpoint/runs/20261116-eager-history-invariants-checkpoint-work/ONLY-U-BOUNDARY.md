# Remaining pending-domain boundary

OnlyOriginalUPending restricts boundary atoms. It does not require a pending handle
to equal the original U handle. InternedBoundaryAtoms.lean:19-24 ignores ordinary
node and union identities. ClosedResetProfile.lean:29-30 uses this atom restriction.
Fresh native handles alone do not establish a counterexample.

At done, the relevant normality and decoded-domain facts make this restriction
strong enough to obtain membership for every finite Type. See
SourceSynthesisCurrentDonePendingTypes.lean:104-120 and
SourceSynthesisCurrentCanonicalUnionTypeMember.lean:105-146.

Actual cold source values and the first direct goal write have proved producers.
See SourceSynthesisCurrentUniverseStartupAtoms.lean:66-77 and
SourceSynthesisCurrentSharedSourceGoalFirstWrite.lean:145-153,177-206.
Incoming and alias merges issue actual native queries and store the returned handles.
See SourcePruningEnumerationSharedIncomingNode.lean:63-85 and
SourcePruningEnumerationSharedDispatch.lean:78-90.

The remaining producer must preserve the pending-domain Profile across the whole
actual worker and its warm native queries. GeneralCMHistory.lean:37-66 gives a
conditional result on its literal initial-node history. SourceWarmEntry.lean gives
actual old-entry provenance. Neither fact is the whole-worker closure theorem.
OriginalInputsThrough and FieldsThrough still need actual admission producers.

No actual-source counterexample is established. If foreign-Mu domains are reachable,
direct membership for each chosen pending value is the more general replacement.
Do not attempt to prove exact handle identity or full-U body identity from atom closure.
