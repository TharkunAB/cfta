# Default Haskell entry: reduced root, derived flag and literal hooks

Status: read-only HEADER/PLAN. No new runtime correspondence or defect is claimed.
The frozen90 mode audit and SII42 candidate audit remain unchanged.

1. Exact Haskell call path.
   Synthesis.hs solutionsOfSize:973-974 = programsIn . orderedSearchSpace lib query.
   orderedSearchSpace:774-775 = reduceWithOrder . rawSearchSpace lib query.
   rawSearchSpace:778-779 builds ofType(relevantOfSize size)(encoded goal).
   reductions:671-684 performs at most30 rounds of
     next = withoutRedundantEdges (reducePartially node), stopping on node equality.
   reduceWithOrder:718-719 = orderedSpace . reductions.
   orderedSpace:724-740 uses births' LAST root, then refoldEdges; spaceNode is folded,
   not the raw root or one reducePartially result. It transports minimum birth rounds.
   programsIn:969-970 maps toProgram over nubOrd(map fst(runsBy spaceOrder "Mu" spaceNode)).
   Enumeration.hs runsBy:1253-1256 -> runsFrom(canonicalEdgesOf(Just weight)).
   runsFrom:1285-1293 initializes THAT root, executes enumerateFully, then marker render
   and residual-fragment render. initEnumerationState:297-311 sets edgesOf(root) and
   checkEmpty=reachesConstrainedMu THAT root. The flag is recomputed after refolding.
   canonicalEdgesOf:708-717 retains initial canonical rows and has a new-node fallback.

2. Literal default control is a separate call-path obligation.
   enumerateFully:913-915 passes unit state, noExpansionPreference and false/unchanged oracle.
   enumerateFully':920-927 calls enumerateUntil' Nothing IDENTITY narrowing enumerateNode.
   CurrentProgramEagerOutputs.accepted:44 instead calls CurrentProgramSlotsInitialization
   ONCE at the raw source build (proof:144-154), then ONE configured runEager worker.
   It admits arbitrary checkEmpty/edgesOf/order, matching keys, graph and templates.
   It retains the actual prepared backend, not a declared literal-default specialization.
   Its worker reaches Action.prepare:17 -> OuterNarrow.narrow:11 -> NativeView.narrowAt:33,
   and SharedPreparedRecursive.continueWith:74 -> recordTypes:50 -> actual restart.
   The actual eager children now close the old shallow-backend gap. They do not by
   themselves erase these hardwired hooks or change the starting native root.

3. Neutral metadata is NOT evidence of inequivalence.
   With templates=[], recordTypes_empty:76 gives pure(false,{metadata with
   types:=updatedTypes metadata uv input}) for EVERY callback input, without a core read.
   pending, typing and openHoles stay exact. Initial pending=[] therefore stays empty
   under these callback updates; packaging the whole-run invariant still needs induction.
   An arbitrary nonempty template catalog is outside this default specialization.
   With stop=None/order=(fun _ _=>None), the extra types list need not be externally
   observable. It still controls OuterNarrow's type skip, so erasure needs a proof.
   Always-true fits/admits retain every row in NativeView.keeps:22, but narrowAt STILL
   runs actual nodeEdges normalization and makeNode. Do not infer physical value/heap
   identity just from filter identity. Prove a same-run core/native/cache/query erasure,
   or factor literal hooks into ONE backend with exact old prepared wrappers. This is
   a required RESULT, not a public neutrality/after-state supplier premise.

4. Existing Lean components and their exact limits.
   CurrentCallerInitialization.accepted:31 supplies ONE current original build/context.
   CurrentComputedWidthSharedCompletion.accepted:46 supplies ONE stable checked nodeCall
   result/after/full Memos, Post/NodeLaw/ValueFields under input-selected mathematical bits.
   CurrentComputedWidthTypedSharedCompletion.accepted_typed:65 observes that SAME result.
   A nodeCall is a native reduction call. It is neither the eager enumerator nor the
   complete30-round plus redundancy/refold preprocessing pipeline.
   RedundantEdges.reduce_exact:88 proves cluster language preservation from its meet law;
   it is not an actual whole-native withoutRedundantEdges/refold receipt.
   ReductionBirthOrder.reductions:447/source_history_bound:463 model arbitrary step and
   observed key lists/pairs. The module explicitly excludes source traversal/refold execution.
   No actual native refoldEdges implementation/correspondence was found in live Lean.
   EndpointReachability.reaches:16 and SourceMemoGate.unconstrained supply the modeled
   Boolean; exact source representation/constraint-read agreement must relate it to Haskell.
   SharedEagerReservation.runEager_finite_complete_resources_program_slots:8167 supplies
   the configured worker's entire stable/resource/per-output roles from CURRENT inputs.
   initial_packet:31 plus Roles.initial_program_slots:63 already attach current Context,
   available closed value and ValueFields to one initial handle/cache. No model is needed.
   SharedEagerOutputControl.runEager_output_control:454 supplies finishedness on SAME run.
   ProgramRolesPartialCompletion.complete_program_root:32 then supplies actual root readback.

5. First genuine new bridge and preservation requirements.
   Model/verify the literal bounded preprocessing from the SAME source build, threading
   each caller, issued heap, constraint cache, inventory and ALL returned Memos. No rerun.
   Compose per-pass NodeLaw with actual redundancy and refold language equivalence to
   keep original-root membership in BOTH directions. This does not imply nonemptiness.
   Separately preserve ValueFields/Program layouts/protected Program positions across
   preprocessing. Language equivalence alone cannot give physical slot roles on empty domains.
   Carry full source-row/guard/child provenance through each edit, deletion and refold map;
   an equal label or independent row witness does not identify the causal source ancestor.
   Derive the actual final flag and selector from this SAME processed root. The generic
   selector member/length bounds allow subsets; default all-row order needs permutation,
   canonical fallback, transported births and the concrete finite Double weights.
   Derive initial Packet/roles at the resulting caller using existing startup APIs, then
   invoke ONE eager role worker and ONE root consumer per SAME emitted output.
   Recompute/join capacity for preprocessing AND enumeration from original inputs;
   raw enumBits cannot be reused at an enlarged heap without a new profile comparison.
   Fixed Haskell Int/global interning, lazy execution/order/multiplicity and depth-free
   runtime versus chosen finite recursiveFuel are still separate correspondence obligations.
   The sketch file lists required returned facts, not assumed future providers.

6. Suggested FINDINGS scope wording (parent owns any edit).
   CurrentProgramEagerOutputs proves resources and Program readback for the configured
   shared eager worker on its original raw source build. The default Haskell API first
   reduces/refolds that build, derives its flag/order from the returned root, and uses
   identity narrowing plus a false/unchanged oracle. The preprocessing and observational
   hook-erasure links remain unproved. Pure metadata updates alone establish no behavioral
   difference. This corrects coverage scope; it is not a new Haskell defect or counterexample.
   Model existence, original-input completeness and all default runtime claims remain open.
