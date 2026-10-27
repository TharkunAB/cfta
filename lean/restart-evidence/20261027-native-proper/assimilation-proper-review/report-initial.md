# Native assimilation and adapter ProperState

Status: bounded source assessment and immutable v1 draft complete. The draft is UNTESTED by this reviewer. Root owns all compiler checks. This bundle remains OPEN for final installed-source, public and document review. No old frozen area was changed.

## Actual missing-handle origin

The generic CachedAssimilation.finish accepts an arbitrary merged Option. Its complete theorem only requires readback when that Option is some handle. That condition is vacuous for none. It therefore does not by itself preserve ProperState: a caller could pass none while the concatenated old buckets are nonempty. The resulting pure-none slot would be improper. This is a limitation of that generic API, not a demonstrated reachable Context/Packet or Haskell defect.

The actual Dispatch worker has the required origin:

- If the source node is none, the optional branch uses the original target node.
- If the source is some handle and the target is none, it uses that source handle.
- If both old nodes are present, an actual successful native query and enabled-check phase must encode a replacement. The action is Assimilation.finish with that literal encoded handle, so it writes some handle. An Empty replacement rejects before either raw write.

Thus an actual successful merged-none row can come only from two original none nodes. Original ProperState forces each original suspended bucket to be empty. Their concatenation is empty. For a some-handle result, both original buckets contribute only proper tries; a none input contributes no entries.

## Draft interface

`drafts/v1/SourcePruningEnumerationDispatchProper.lean` exports one theorem in the actual Dispatch namespace:

`dispatch_proper checkEmpty nativeFuel p h beforeCaller before source target queries action afterCaller savedQueries after proper selected completed : ProperState after`.

The argument order matches dispatch_canonical. It replaces only the initial Canonical property with ProperState; the exact actual dispatcher triple and raw successful singleton premises are unchanged. It is an observation theorem at every fixed fuel, not a new producer with a supplied future completion gate. Existing original completion producers provide these observations when composed with this theorem.

The proof follows the actual existing DispatchShape.singleton runtime cases. It does not consume that theorem's existential merged witness, since that exported witness omits the none-origin fact. The optional branches establish the required origin directly. Native branches write a literal some handle. Two private structural helpers extract proper paths from the original payloads and prove preservation through target replacement, source elimination and the ancestry-only update. There is no Graph, desired final ProperState, query semantic law, Context, universal Ranges or arbitrary continuation law in the public theorem.

V1 has 227 lines, 15549 bytes, SHA256 `7c6763e825bd3bfabaa3de85d3f7664aa613f47f9e8ecab1e7fbf90d0cf66a74`. No compiler or runtime execution was performed here. An initial draft-generation assertion had a mismatched source string and wrote no draft; the final immutable v1 uses the exact source conclusion boundary.

## Adapter and composition boundary

Root owns the cached adapter/Fold lift. The actual CachedAdapter.adapt returns the original cache for raw[], same source/target and an eliminated source. For a supported singleton it either returns that original cache or attaches the actual returned core. Other raw shapes attach no cache. Its existing canonical proof can be reused with ProperState after replacing its leaf dispatch_canonical by dispatch_proper. The helper that assumes a property of the current raw singleton must remain an internal adapter lemma; the actual public run theorem must derive that property from the actual Dispatch observation.

This adapter has no synthetic Empty write. Its raw[] branch restores before. Do not confuse it with IncomingCacheAdapter, whose separate logical Empty write is handled by the incoming worker proof. Native caller/query effects remain those of the actual dispatcher even when the enumeration cache is restored. This proof does not infer Safe, native heap equality or full Memos equality from ProperState.

EnumerationProgress.intersection_proper and assimilate_proper are graph-worker results. They cannot justify the native worker by introducing a fabricated Graph equality. The new direct proof uses their existing ProperValue definition and the actual native action shape instead.

A successful local ProperState preservation result does not derive the original condition from Packet or Canonical. Root must still compose real incoming writes, child preparation, traversal, captured finalization, callbacks and actual recursive histories. No whole-history origin or positive-output coverage is claimed here.

## Provenance

`source-index.json` preserves nine exact whole source identities and fourteen literal cuts. The cuts pin ProperValue/ProperState, graph reference behavior, the actual native optional/query branches, generic cached finish, dispatch singleton shape and cached adapter reconstruction. No repository file, compiler, build, Git state, network service, board or older frozen bundle was changed or executed.
