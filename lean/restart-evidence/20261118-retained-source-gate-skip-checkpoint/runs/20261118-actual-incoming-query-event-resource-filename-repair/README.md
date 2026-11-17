# Incoming query-event resource filename repair

Status: FROZEN UNCOMPILED CANDIDATE. Root rejected the original packet during
preflight because its filename already names a normal Source module. No compiler
failure is claimed for that attempt. Keep the original packet immutable.

Select SourcePruningEnumerationSharedIncomingQueryEventResources.lean as the NEW
normal module. Its complete source bytes equal the original 6cf23993 candidate.
All public/private FIRST headers, both proof bodies, preamble and probe fixtures
are byte-exact. Only the source artifact name and module metadata change.
The public QName remains SharedIncomingQueryEvents.observe_query_resources.

The existing normal SourcePruningEnumerationSharedIncomingQueryResources.lean
must remain unchanged. SOURCE-PINS binds its complete current bytes. It remains
a normal transitive dependency. Do not exclude it from a fresh namespace as a
candidate output. Exclude only the corrected EventResources output name.

This is one public theorem and one private helper, with zero new definitions.
PROBES selects one public axiom report. INTERNAL-PROBES is optional owning-module
private evidence. The original leaf's all-outcome event/resource scope is
unchanged. No worker-wide resource or finite-model claim is added.

No compiler, normal Source, active Work, Git or runtime action ran here.
