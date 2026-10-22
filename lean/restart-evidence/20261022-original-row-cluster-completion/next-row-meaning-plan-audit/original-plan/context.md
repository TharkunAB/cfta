# Context and source scope
The literal RowLanguage API requires the current concrete formula symbol and guard types. Arbitrary holds and an arbitrary admitted input model remain supported.
Reuse SourceCurrentAllocatedNativeContextCache, SourceRecursiveIntersectionGuardedInput and InternedNormalizationFree public APIs; use SourcePhysicalSharedRowsLanguage.all₂_both_imp if it is not already in the import closure.
An exact import/namespace/notation block belongs to the later declaration-review step. This file deliberately gives no Lean context or theorem header.
Public payload_readback, copy_readback, Original.codec and closed_readback replace any call to an imported private helper.
OriginalInput.child is a checked witness producer; its result is not automatically admission by arbitrary inputModel.valid.
The parent-valid premise derives all exact row-child admissions. Empty child lists impose no additional admission obligation.
Ordinary closed-parent scope matches the current ordinary branch. This adapter does not infer closedness of a Mu body or support generated parents.
