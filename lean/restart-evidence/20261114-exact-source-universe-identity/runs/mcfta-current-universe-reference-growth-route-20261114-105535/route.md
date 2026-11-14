# Exact universe identity after source heap growth

Status: header and proof route only. UNCOMPILED. The current source-heap identity remains public at 7501e8c433b9a9fffa2511e2b742c185f2d00985.

## Existing native replay requires a later starting point

SourceRecursiveIntersectionKernel.execute_replay and execute_larger_replay require Extension from the completed call's final machine. They cannot use Grows from the original source heap alone. The completed call can allocate product rows and domain entries. Requiring their presence would add an unproved result condition.

## Reuse the existing proof once

Generalize the existing main proof over sourceHeap and current heap. Keep all five existing private helpers unchanged. Move the current main proof to the new after-growth theorem. Replace the old proof with a reflexive-growth wrapper. Preserve the old theorem header exactly.

The new theorem accepts the same accepted source expression, one actual closed build, and one observed original full Mu. It also accepts Facts for the current heap, Grows from the original build heap, and an arbitrary valid current domain cache. It accepts no product, callback result, current source build, identity result, future provider, or source-call-final extension.

1. Transport the original stored record through Grows. Current Facts.cached derives the complete original Mu availability. Its owner reference is available by the existing private helper.
2. Use the checked same-writer body replay at the actual current heap. Compare it with the actual C8 callback there. This retains the full original body and all current raw body row records.
3. Use the existing public original-heap probe row packets. Transport their raw edge residency through Grows. Derive each current complete probe availability from the original stored Mu's children.
4. Transport the original marker's complete node record. Current Facts.cached derives its availability. Apply the existing generic marker equality at the current heap.
5. Reuse the checked mapped body algebra, product-to-probe replay, exact original Mu key readback, ReferenceIdentityJoin, and larger-fuel stability proof.
6. Derive original root availability with InternedFreshOrdinaryReplay.empty_replay and build_verified at the current heap. This is replay of the same actual build into a warm heap. It does not introduce a second cold build or an input receipt.

Facts + Grows do not imply preservation of every orphan issued reservation. The proof does not need that stronger claim. It reads the required complete original record from the current cache and derives its actual current child availability.

## Coverage and semantic heap boundary

Arbitrary structural growth can add unfinished keys or records that violate semantic normalization. Current Facts and Grows do not establish Covered [] or SemanticHeap. The new theorem proves their preservation as implications in its conclusion. Neither invariant gates identity completion. Existing native execute_covered and execute_scoped discharge those implications.

The old theorem applies the new law at reflexive growth. Its actual closed build supplies closed_covered and SemanticHeap.constructed. Its full old coverage and semantic conclusions remain unchanged.

## Actual stage obligations

To apply the new law after enumeration or preprocessing, derive Facts current and Grows sourceHeap current from that stage's actual effect chain. Supply the actual valid domain cache. Derive Covered pending current and SemanticHeap current separately when the stage requires those resource conclusions. No future result or provider is needed for identity itself.

This does not prove closure of arbitrary generated types, global finite witnesses, a full outer memo/caller run, or Haskell correspondence.
