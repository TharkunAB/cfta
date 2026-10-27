# Native outcome observer draft

OPEN. The v1 source is an uncompiled draft. Root owns all compiler checks and repository changes. No earlier frozen area was modified.

The source search found bare SourceEqualityNativeDemand.done_trace and execute_steps. Those retain actual unannotated Steps. They do not recover rich physical Inputs from bare execution. PhysicalExecution.execute_invariants retains physical validity and heap Keeps from InputsThrough, but does not expose the exact shorter terminal prefix. Existing completed rich-trace readback splits actual bind calls, but does not classify every finite execute outcome.

The draft execute_readback derives the rich observation directly from the actual InputsThrough plan. The induction follows only actual yielded steps. A yielded result has a rich Trace of exactly the supplied fuel and the returned current Inputs. A completed result has a strictly shorter rich trace to the same literal pure value and returned whole state. Every failed, constraint-error or blocked result has a strictly shorter rich prefix, the current Inputs and the literal final step to that exact result. The final terminal step is not silently replaced by a yielded trace.

The draft terminal_step_heap takes current Good, Heap, Inputs and the actual non-yielded-step classification. Generic constructor Work always yields, so that instruction cannot be a terminal step. Optional binding can change the heap before a pending result. The proof uses its actual primitive preservation lemma with current Available and current Facts derived from Good. Node demand, edge demand and checked edge bodies retain the literal constructor heap. The other terminal instructions retain it by their definitions. This is not a claim about arbitrary generic yielded Code or arbitrary continuation arity.

Root can apply its forthcoming query-prefix Heap theorem to the exact rich prefix. Existing rich trace effects can derive current Good from original Good and the actual original field condition. For failed/error/blocked results, terminal_step_heap then preserves Heap through the literal last step. For done and yielded results, the actual rich endpoint already is the returned state. This does not derive a physical plan from bare execute=done, prove query termination, or change any older admission.

No compiler, build, Git, network or board operation was run by this reviewer. This bundle remains open for Root check receipts and immutable source revisions.
