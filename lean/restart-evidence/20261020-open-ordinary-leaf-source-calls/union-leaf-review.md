# Actual closed-union leaf normalization boundary

Reviewed 2026-10-20 16:19 CEST. This is an author reread of the constructed witness.

The source syntax is finite and uses Nat symbols and Bool guards. The first source is `binder false (node [mk 17 true []])`. The second uses symbol 19. The inner source is their union. The outer source is `union [innerSource, var 0]`. It executes with the available literal Depth reference at slot zero and the empty initial heap.

The theorem derives joint Context from empty Context and actual Depth availability. It retains the exact Entered.depth callback receipt. It retains actual completed builds for both Mu sources in sequence, the inner source, the parent buildMany with exact original outputs `[innerValue, reference Depth]`, and the raw outer source. It also retains the actual whole Depth callback. That callback filters after the raw build and returns innerValue at the outer return heap. The raw build and the callback result are different stages.

The first two results are distinct closed complete Mu records. Their local binders are unused, but smart=false retains those records. The actual inner union retains both as opaque members and is closed. Therefore its leaves stop at `[innerValue]`. The raw outer union flattens the inner union beside Depth and remains open. Its leaves include the first whole Mu record. That record has an actual structural RowAt with symbol 17. It belongs to neither `leaves innerValue` nor `leaves (reference Depth)`.

The sole public theorem explicitly negates the general member-leaf membership statement for these actual original outputs. It refutes a weaker claim than same-index descent and therefore also blocks that stronger claim. It does not refute preservation of a row through structural RowAt or a more precise normalization route. It does not claim unique ancestry, productive recursion, semantic observation equality, completion, a Haskell defect, or a failure of existing production theorems.

A correct future union handoff must account for the closed-root stopping rule separately from union flattening. The same whole leaf need not belong to any original member's leaf list. A source row or exact union-member normalization route may still provide useful ancestry. Encoder slot and leaf occurrence indices remain separate.

The private checked_witness and the public theorem have identical expanded statements. The public proof is an alias to that checked witness. The first two strict attempts failed on proof elaboration only: existential Mu witnesses and unavailable Decidable equality on whole Values. The final proof uses actual physical identity comparisons for disequalities. Strict attempt 3 has a literal zero-byte log. Full public attempt 1 prints the complete statement, proof alias, and axioms without omissions. Only propext and Quot.sound occur, within the standard three permitted axioms.

All four Lean jobs have fresh usage receipts, a five-minute cap, memory.max=memory.high=4294967296, and zero swap. All attempts are retained. There was no canonical build and no repository write. The prior node-leaf package remains unchanged.

The first non-Lean archive verifier rejected the zero-argument theorem's printed name because it expected a leading @. The probe source correctly uses #check @. Lean prints that theorem name without @. The verifier accepts both printed forms. The rejected verifier, manifest, empty verification output, and error record are retained. No Lean source or proof receipt changed.
