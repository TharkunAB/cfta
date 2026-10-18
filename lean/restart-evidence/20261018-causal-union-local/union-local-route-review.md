# Fixed-reader union local route

Reviewed on 2026-10-18 at 21:19 CEST. This is a source-grounded design audit. No production file was changed and no Lean job was run. The route below derives a per-pair literal/local constructor law. It does not assume Directed for the relation that it aims to build.

## Why immediate Local is too weak as the source member hypothesis

SourceDirectedCases.Local tests a bare root reference, immediate nodeEdges, and each immediate epsilon successor. A member reconstruction can be a union with no immediate nodeEdges and still contribute literal ordinary rows to its parent. Actual makeUnion can flatten that union or merge its ordinary members into one node. The original intermediate node need not be reachable as a complete value from the parent. Thus a strict member's immediate Local row clause alone does not transfer the row that normalization exposes. Calling Directed.row on the source relation at this point would assume the missing global result.

LiteralRootParts.Literal follows only root unions and keeps complete Mu values as atoms. Row follows only root unions and keeps full ordinary rows. LiteralUnionParts.literal/row prove exact preservation of these parts by actual normalization. LiteralUnionFusion.warm proves exact literal parts after actual warm stored member and parent calls. These theorems retain complete guards and ordered children. They do not identify a Mu's unfolded body with a literal ordinary row.

## Smallest faithful stronger interface

For a fixed reader F and relation R, use three one-way clauses for an endpoint pair (left,right):

1. Every literal reference of left has ReferenceOrigin F [right] at the same name.
2. Every literal ordinary row of left has an Origin F [right] row with the same symbol, complete guard, and ordered Mutual R children.
3. For each complete literal Mu atom of left and each ACTUAL successor of that atom at F, there is a reached endpoint from right at F in R with that successor.

This is a source-constructor induction hypothesis. It does not quantify over all row origins or demand a global Directed instance. The Mu clause retains the actual reader execution. It does not inspect or assume the selected writer's desired output equivalence.

Use R = Closure (Generated F OR Below). Equality and Below have these clauses directly. Ordinary source-node results have no literal reference or Mu obligations, so their already-derived node Local row law supplies this stronger interface. Full literal clauses plus actual R left right imply immediate Local F R left right: the union epsilon successor is a genuine literal Below fragment of left, followed by the existing parent chain; a Mu successor uses clause 3. This conversion is a per-pair result. DirectedClosure.directed alone does not prove that all chains have local clauses when the generating clauses already use R. The global relation proof remains separate.

## Actual common-reader schedule

Start with both real historical Contexts and successful builds of the same source union, raw return Grows into a Ready reader, raw-parent Available, replacement maps and History empty reader. Keep all historical lexical facts at their real entries. Do not derive Values reader inputs from Grows.

GeneratedUnionPreparation.source_members derives all original source-member values at the reader. Primitive references use the exact parent free-name support. Resident nonprimitive values use retained nodeRecords and the reader's recursive cached availability. This distinction avoids an invented issued-name extension.

Run finite actual member filters and stored calls for the first side, then the second side. Keeps supplies actual readiness, availability, issued-name retention and replay into the common final F. CausalUnionPreparation derives the local publication histories from actual filter NoNewMu effects and completed stored calls, then composes History empty F from the initial history. It needs no history of the earlier original source-return heap. Replays make both parents and all indexed member schedules warm at F. Determinism can identify these parent endpoints with the original warm parent results when those were supplied.

GeneratedGrowth.generated/inputs transports generator membership to F. It does not transport finite observations or Origin back to the starting reader. The theorem must conclude at the produced F. If an old-reader observation is needed, prove a separate WarmSupport transport. A larger reconstruction reader is not the original reader.

## Constructive union step at that fixed F

1. Recover the original member lists and indexed historical child source Context/call receipts from the actual union builds. All lists keep the original order. Restrict Aliases and full Scope self tests to each source member. FilteredUnionFusion.scope_subset shows the required support inclusion, including the Depth anchor.
2. Use UsedBinderOutputTags.bare on the actual child and parent source equations. This proves parity of the exact retention test: raw child is not bare own, OR the complete raw parent is bare own. It is not enough to test whether a member merely contains self. Standalone self is retained; self inside a larger root union is removed.
3. Invert FilteredUnionFragments.parts. Each selected parent literal atom or row has an ORIGINAL member index, its actual raw/cut/output values and the retention test. Match the same source index on the other side. Duplicate values do not erase the source occurrence.
4. Apply the genuine strict-source member literal clauses to these actual member calls at F. This transfers a literal reference, full row, or actual literal-Mu successor to the opposite member result.
5. Use GeneratedUnionCases.retained_member to derive Below oppositeMemberOutput oppositeParentOutput. This follows from actual normalization, filtering and stored calls plus the now-derived opposite retention test. It is not an assumed output relation.
6. Lift the opposite member observation through that Below fragment. For references use the already-proved Directed Below reference transfer. For rows use its row transfer and compose ordered RowMatch children through Mutual R. For a Mu successor use its path transfer and append the resulting Below endpoint to R. Only genuine Below uses a Directed theorem. No Directed Generated or Directed R is assumed.

The constructor IH must supply literal clauses at this SAME F. An IH that merely produces clauses at a still-later reader does not meet this contract. For the eventual whole-source theorem, a variable member can return an arbitrary resolved Generated lexical pair. Its local clauses need the mutual Generated/Inputs derivation IH or a proved lexical source law; source-size induction alone does not supply them.

## Existing normalization boundary

The preserved actual grouped-union witness has u = makeUnion [rawMuA,rawMuB,z] and v = makeUnion [makeUnion [A,B],z]. Both are available at a source-built Ready reader and have all finite Same observations. It has a genuine positive Directed instance but no old two-way Forward relation containing the pair. This rules out demanding mutually related epsilon endpoints. The inner grouping is essential: makeUnion [A,B,z] does not merge A and B when z prevents the all-ordinary branch.

## Source pins

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `lean/MicroCFTA/SourceCurrentLiteralRootParts.lean` | 2906 | `d2d0bddaf1aa4f3397505ca751915b04ebf190a528c8c27db53255c29cbea4df` |
| `lean/MicroCFTA/SourceCurrentLiteralUnionParts.lean` | 10782 | `7284dfe74faa0eea227fce87867ef5377f525ee5726f1b4a19200487d5b6f7d3` |
| `lean/MicroCFTA/SourceCurrentLiteralUnionFusion.lean` | 13965 | `7722dd4c8f5833ed531c924eb8a151019aea29d9a5401c0fa4be7bd842863bea` |
| `lean/MicroCFTA/SourceCurrentLiteralFilterParts.lean` | 11203 | `5db5739dd40775b0fe49a4e0ae44d1b3d5ae22ed8b86ab6d366bac27baf8cdbb` |
| `lean/MicroCFTA/SourceCurrentStoredLiteralExecutionParts.lean` | 15701 | `7358fa81687b0eac78479b96f55b7a850d916ae34a22565c95461cfde3b4c3f6` |
| `lean/MicroCFTA/SourceCurrentSourceDirectedCases.lean` | 28890 | `f770d8bd236b7b2b8c66cf75b3b1c108e2835afa5f8999b9dadf52923d5c0888` |
| `lean/MicroCFTA/SourceCurrentGeneratedUnionCases.lean` | 6174 | `aa894cb760a5b7efb193dc49fee1eb322ac3b8e38cc59be145dfd6c76df69b47` |
| `lean/MicroCFTA/SourceCurrentGeneratedUnionPreparation.lean` | 20121 | `1b5a74f38cb29a5eeb75bd4e6193abc0f5b91ea5002fc5c347aa68ca2b27a33e` |
| `lean/MicroCFTA/SourceCurrentGeneratedGrowth.lean` | 4855 | `010da32c20a7f0e51fd7a941f72b75eda84ec8c3393fe8ba3e47a8c69ed46643` |
| `lean/MicroCFTA/SourceCurrentFilteredUnionCoverage.lean` | 13011 | `1bb154e21f58b71cf7b1fb72a53571f125f3fde1494c001020c0111e9051b390` |
| `lean/MicroCFTA/SourceCurrentFilteredUnionFusion.lean` | 18999 | `6bce98886e8af81a077351713db49cd714d2de7b6e056fa8b6f403db8d4cb24c` |
| `lean/MicroCFTA/SourceCurrentUsedBinderOutputTags.lean` | 29723 | `249b06a358eac40de2451a591566f679ebb02d5be7edbd7432b9633e8b5a5d27` |
| `lean/MicroCFTA/SourceCurrentUsedBinderAliasTransport.lean` | 26779 | `192ccb08a7322c3619781b3886ce491f0a4b72b2914e14d108212d9c29171d2e` |
| `lean/MicroCFTA/SourceCurrentDirectedClosure.lean` | 7574 | `96b94082cf4c8fb1aa7cec62023d5a9f6db59e09884d8e1016d1af5676067a54` |
| `lean/MicroCFTA/SourceCurrentOpenPreorderSimulation.lean` | 6136 | `080dce05c66ea21a6971e0b07d866361b894b3aa3f7d05ea525985ef50ac32fa` |
| `lean/MicroCFTA/SourceCurrentCausalGeneratedEmpty.lean` | 6206 | `744a576b5218ae54d27847b7ad590de532756b4130f54861859a154631ef89cd` |
| `lean/MicroCFTA/SourceCurrentCausalGeneratedNodeLocal.lean` | 14269 | `5fe61e23ba1de494d15fc044fdd99e769797c9b50c26f0be8e399850a49bc3f7` |
| `lean/MicroCFTA/SourceCurrentObservationReaderSupport.lean` | 20347 | `55987adb8612f53211574abf9651ca96498582aee336d4deed225e2cc119abf7` |
| `lean/MicroCFTA/SourceCurrentRetainedMuDirectedCase.lean` | 24892 | `05d0aee93c334dac44fbf924590677885608657b352cfa7cb9eb14dd7b345282` |
| `lean/MicroCFTA/MergedFreshOrdinaryGraph.lean` | 4336 | `00d74646b29174976b2fb0b65dd0af4ae309deee31d35ac8591fed6e303f99a4` |
| `lean/restart-evidence/20261018-open-binder-source-induction/preorder-normalization-review-kernels-5.source.lean` | 19555 | `e3ddfcd05d9366320671241d81b626ec5c7a3e3947e2c36a1d2e43903c8db027` |
