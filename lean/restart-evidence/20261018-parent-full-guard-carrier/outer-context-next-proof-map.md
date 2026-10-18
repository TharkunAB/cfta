# Outer sibling context and resource transport

Read-only review on 2026-10-18 at 06:49 CEST. No new Lean module or check ran. The current pull and integration belong to the root task. The accompanying manifest pins the exact source bytes read here.

## Finding

There is no missing small prefix or descent adapter to implement. SourceCurrentInheritedNumeric already constructs the literal inherited prefix and indexed descent with full Frame, unchanged physical Fits, and same-stage-inventory Post. SourceCurrentRawRebuildNumeric already handles raw node and edge reconstruction with complete Frame and a constructor profile. Adding OuterPrefixContext for those operations would duplicate public results.

The first remaining semantic step is a mutual successful-outer-call induction that returns the semantic context, full query Frame, scheduled Fits, and actual graph/reads together. Its sibling branches must consume those returned facts before the next call. Existing physical prefix transport alone does not prove them.

## Exact branch boundaries

SourceCurrentAllocatedPartialWorker.rows performs, in order:

1. edgeCall on the original head row at the entry caller;
2. descendants on the returned Parent row at the returned caller;
3. rows on the original suffix at the descendants return.

The original inherited payload stays the same across all three stages. The suffix rows are original rows, not the new Parent rows. SourceCurrentOuterPrefixInvariants.step_good, rows_tail case, already derives their residency by total heap growth and retains EqReady by operation growth. It also derives physical Good. It does not derive a semantic Context or the strong Frame at the suffix caller.

SourceCurrentAllocatedPartialWorker.walk performs literal descend at the current operation cache, calls nodeCall with the actual descended payload and original head value, then calls walk on the original suffix with the original combined payload and index + 1. The suffix must use the returned full caller and the original combined payload. It must not use the child payload as the next combined payload. The physical walk_tail proof already preserves suffix availability and the original combined EqReady.

SourceCurrentAllocatedPartialWorkerActual.walk_step and rows_step show the existing correct semantic composition. They invert the actual equations, derive strict graphs and reads for each smaller call, obtain the actual returned Post, and feed its context and global memo bundle to the suffix. They also retain the complete caller states and evolving inventories. Their WorkerRanges inputs remain the unresolved premise for the proposed initial global schedule. They are useful proof templates, not initial resource producers.

## Available producers

* SourceCurrentInheritedNumeric.resident_complete supplies own-field lookup from current residency. It returns the actual combined payload, Frame, unchanged physical Fits, and Post. Inherited contradiction needs neither residency nor field lookup.
* SourceCurrentInheritedNumeric.descent and prefix_descent retain the native state, strong Frame, physical Fits, all outer tables, Merge, and fourth memo. They derive the actual child EqReady.
* SourceCurrentActualEdgeCallSemanticReads.edge_call aligns an initial numeric edge receipt with any observed successful literal edgeCall. Its initial Context, Frame, Fits, resident row, EqReady, and pure initial reservation are real inputs. It returns the complete receipt at that exact result and full caller. No observed-fuel comparison is needed.
* SourceCurrentActualParentSemanticReads.parent and edge_body provide the same alignment at the Parent or body boundary. They construct the numeric completion first and use successful-return uniqueness. They do not derive the caller context at an arbitrary earlier recursive entry.
* SourceCurrentAllocatedPartialCallSteps handles begin/finish protocol laws. Publication and finish leave checked state unchanged. Finishing a node still requires the actual derived node result law; physical result residency alone is insufficient.
* SourceCurrentRawRebuildNumeric.edge/modify preserve Frame and derive constructor Fits from actual available replacements. SourceCurrentOuterConstructorBounds.children_rebuild/rows_rebuild add exact successful worker length laws and finite flat guard retention.
* SourceCurrentMuReconstructionEffects.node_body proves actual resident Mu cleanup returns at the same full caller from initial physical Good, ProbeHeap, and availability. SourceCurrentOuterConstructorBounds.mu_body retains physical Fits and carrier there. This branch introduces no additional recursive Parent call.

## Proposed next proof

Use one mutual proof over literal outer fuel and its finite phase order. For each observed successful node/body/rows/descendants/children/walk return, derive an actual graph, strict Reads with the exact initial/final global memo bundles, the old semantic law and Post, final Frame at the same returned inventory, and Fits plus a finite raw-guard carrier at a pure initial phase forecast. The observed equation is the verification boundary; no successful future child call, reached-entry reservation callback, or desired result law should be an input.

At rows_tail, combine the derived edge Post and descendants Post, then pass their returned inventory, Frame, Fits, global memos, and carrier to the suffix IH. At walk_tail, first compose descent Post with the derived node Post. Retain the original combined value by operation growth. The smaller node IH must supply its NodeLaw before finishNode installs a semantic returned cell. The outer memo Context cannot be reconstructed from physical Good and a guard carrier alone: Good checks captured operands and resident outputs, while Context.sound also checks returned language laws.

The pure forecast must include both the new complete Parent carrier/profile step and non-Parent constructor steps. SourceCurrentOuterCallBudget bounds only entered Parent sites. It does not count raw node/edge reconstruction, inherited prefix allocations, or indexed descent. Reusing its count as a bound on all allocations would be incorrect. A full phase recurrence can bound these additional events directly from outer fuel, without any returned source-height assumption.

This is a substantive mutual proof. A two-line wrapper that assumes the returned Context, Frame, Fits, or smaller-call preservation would leave the immediate obligation unchanged, so no such module was added.

## Equality-operation resources outside physical Profile

SourceCurrentAllocatedNativeResourceForecast.Profile has only nodes, edges, domains, and stored payload mass. GeneratedQueryResources.Fits checks exactly those four components. Inherited prefix and descend can therefore keep Fits unchanged while their equality interner and completed operation tables grow.

SourceEqualityConstraintMemoAllocation.State separately contains constraints, combinations, and descents. A combination miss can intern its actual normalized equality payload and install a completed combination cell. A descent miss can intern its child payload and install a descent cell. Accessor/precheck and native conjoin/empty-field construction also use this interner. SourceCurrentOuterExecutionGrowth.reached derives actual Cache.Steps and table extension, but no upper bound on the equality interner next counter, installed operation cells, or total equality-payload size.

For the current Lean model, these are unbounded Nat identities and functional tables. There is no additional machine-capacity guard in combine or descend that a physical Room proof secretly discharges. A finite runtime or complexity theorem would need a separate equality-resource account: initial interner supply, allocation attempts at actual accessor/combine/descent/native-conjoin sites, completed-table support, and payload/path/class work. This must include the initial inherited payload, whose size is not bounded by physical heap mass. The new Parent guard alphabet can bound its own raw-field cases; it does not by itself bound an arbitrary initial inherited payload.

The live Haskell equality cache uses a separate Int identity supply (cfta/src/Data/CFTA/Equality/Constraint.hs:265 and :280). Cache.nextId uses atomic fetch-and-add on Int (Interned/Cache.hs:89). A host refinement needs a no-wrap/identity-adequacy premise or a derived whole-run bound for that separate supply. This observation identifies an existing refinement obligation; it is not evidence of a new runtime defect. The abstract outer keys retain inherited Option Nat identities without a packed-width check, so physical node/domain Room is not an equality-id capacity theorem.

## Scope

This map preserves the current actual graph, strict reads, global bundles, full caller, and returned inventory boundaries. It does not prove general outer termination, exclude active node-key collisions, or supply the missing initial whole-run resource recurrence. No production, old evidence, Haskell, Audit, or authority document was changed.
