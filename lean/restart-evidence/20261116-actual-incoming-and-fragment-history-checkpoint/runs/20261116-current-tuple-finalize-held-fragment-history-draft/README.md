# Local tuple and finalization held-fragment receipt

Status: UNCOMPILED. Root alone runs the checker.

APPEND.lean.txt adds one private theorem to the existing resource owner. Append it after the full pinned owner. Append PROBES.lean.txt in that same owning file for the private name. The owner already imports OpaqueSuffixIsolation. Root installed the exact public HeldFragmentHistory ABI there. No new import or visibility change is required.

The local theorem retains the tuple's exact original and reached caches, caller, heap, and supplied finalizer fuel. It adds the authorized past captured pending lookup and captured-different-from-held condition. It concludes the complete concrete HeldFragmentHistory receipt.

The proof derives held protection and reference avoidance from TupleInputs. Fresh-reference separation uses the original Safe and held storage bound. Tuple expanded origin prevents the original pending captured slot from becoming expanded before finalization. The actual finalizer changes only captured and ancestry. It therefore protects the held slot and every earlier expanded slot. Returned tuple fragments avoid the held class, so the final written parent fragment also avoids it. HeldFragmentHistory.trans composes the tuple and finalizer receipts.

All premises, including the extra past conditions, still need genuine source producers for the full worker theorem. ActualFrameLedger.captured provides a past pending lookup before own allocation. The actual own-allocation frame must transport it to rowOwn. This packet does not establish that source link or the complete callback/whole-worker history induction.

The original c35 helper and full906/5493 headers are unchanged. Their exact digests appear in SOURCE-PINS.sha256 and ASSEMBLY.json. The full joint finite-completion goal remains open. This local receipt does not construct a model or combine independent assignments.
