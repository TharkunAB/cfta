# Independent controlled-reader review

No material defect was found in the reviewed controlled-vector and reader-step modules.

`HeightOrderControlled.Path` bounds every state's own coordinates by its own control number. A successor must strictly decrease the high-priority lexicographic vector. Its control number must increase and must not exceed the monotone control function. The path does not assume that later lower coordinates fit the initial control number.

The private `blocks` proof retains the highest coordinate along lower-coordinate steps. It splits at the first strict highest-coordinate decrease. The `top_bound` induction bounds the lower-dimensional prefix, then applies the control function at the actual boundary. The top coordinate can decrease at most its initial value. The recurrence includes one block for each value, including zero. Dimension zero has no strict step. `Path.final_le` and `Path.elapsed_le` therefore imply the stated path-length bound. The proof permits arbitrary lower-coordinate growth within each actual next control.

The two external vector kernels are substantive numeric checks. One constructs nine steps from initial control 1, resets a lower coordinate to 7, and exceeds the naive initial radix bound 4. The other constructs a refill and full countdown for an arbitrary monotone strictly growing control function. Neither evaluates the large majorant.

The actual reader relation has no reference or empty-pending successor. Its six cases match the repaired collector. An ordinary head emits rows. An unseen union prepends members in literal order. An unseen Mu stores the actual successful unfolding equation. Visited cases skip only the matching numeric identity.

`Step.good` derives the next semantic, coverage, depth, degree, availability, and closedness facts. The Mu case derives a lower-degree allocation law from the actual unfolded value. `Step.fits` uses current causal mass and the actual unfolding bound. It controls the new heap counters and literal pending work. `Step.decreases` uses the existing dynamic Mu inventory; it does not bound future allocations by the original node count. The static initial mass bounds the number of degree coordinates separately.

The two external reader-control kernels build their own closed source. They exercise productive Mu unfolding, new node and edge counters, an ordinary row emission, a visited Mu skip, an actual union expansion, and a visited union skip. Their final source and logs are frozen. These four external kernel pairs are reviewed evidence; they are not new integration declarations in this component.

This component performs seven new imported full-signature and axiom checks. The two reviewed modules and all four external kernel pairs use only standard axioms. The production strict logs are empty. Canonical logs retain the earlier unrelated dependency warning.

The review also read the draft numeric composition without freezing its mutable inputs. The proposed route is sound: an independently available qualitative collector completion yields an exact consumed Run; actual Step invariants turn that Run into a controlled path; the initial majorant bounds its true count and final resources; stable reconstruction then selects the computed fuel. The external preliminary Mu unfold in `nodeEdges` needs its own controlled step before the closure fallback. This review does not establish comparison, selection, Merge, Operand, or full constrained reduction completion from initial numeric resources.
