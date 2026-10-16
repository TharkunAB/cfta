# Independent review of the outer profile transforms

Reviewed on 2026-10-16 at 23:33 CEST. No material defect was found.

`SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone.lean:23-54` widens the class path count, input row count, captured forest length, path depth, and height. `parentRows_mono` also widens the number of classes from the effective own guard vector. It uses `GuardLimits.effective_mono`. It does not add an inherited-payload size assumption. Lines 57-70 retain the input row bound and raw guard vector.

`SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers.lean:19-26` follows the actual order in `SourceCurrentAllocatedPartialGraph.lean:85-101`. Each original row first executes its edge call. Descendants then traverse the children of that returned edge. At node height `H+1`, the recurrence therefore uses `parentRows G R A H`, `max A 1`, and `GuardParent.outputLimit G` as the inputs to the smaller-height recurrence. It does not recurse on the original row profile.

The outer `max R` retains the root's original row-count bound. The recursive component bounds the rows of every returned descendant. `nodeGuards_ge` at lines 35-38 retains the parent-produced raw guard bound. This is needed when descendant rebuilding retains the returned parent's raw field. The sentinel branch is covered by the arity ceiling `max A 1`. `ParentShapes.structure_from_reads` derives that ceiling for the same actual parent return at lines 132-183. The stronger path and class bounds come from the original own guard, not the inherited constraint.

`parameters_mono`, `height_step`, and `height_mono` widen the same recurrence. The successor proof first increases descendant height, then widens the parent row envelope at the greater height. It does not exchange the parent and descendant stages.

These modules contain pure profile comparisons. They do not construct an execution, produce a quantitative returned-cell law, bound constructor requests, or derive an outer numeric Plan. A producer must still derive each stored owner certificate from the same smaller body reads before finish. A warm hit must align the captured owner with the requested full value through coherent current readback before it instantiates that certificate. Lower native and Merge store retention alone does not supply that outer law.

The review concerns finite ordinary inputs. It does not cover Mu, explicit union, references, general recursive termination, signed-index conversion, or host forcing and HashMap event order.
