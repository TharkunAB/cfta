# Local unbound Mu optional-prefix classifier

Frozen at: 2026-10-20T19:00:34+02:00.

The sole public theorem is `MicroCFTA.SourceCurrentNativeMuOptionalPrefix.trace`. It consumes an actual UNBOUND compileMu Trace ending at the given optional pair, body, continuation, and checked site state. It derives both literal input identities, an exact one-step domain-enter prefix, its physical Inputs, the full Environment.enter/advance child state, and `fuel = count + 1`.

The unfinished-child arm retains an actual UNBOUND body request Trace of exactly `count` steps to the SAME selected optional pair/body at the SAME site state. It retains the complete equation that appends the compiler's own optional continuation to the inner continuation.

The own-site arm derives the selected pair and pure continuation. Its actual UNBOUND child request Trace returns the SAME site body at EXACTLY the supplied site state. The helper `own_optional` proves that a pure-continuation optional-to-optional prefix has zero steps: pending cannot yield, while a yielded optional step reaches pure and cannot reach another optional control. The theorem therefore assumes neither future owner completion nor a future root return.

The proof takes the first actual physical check from the SAME Trace.cons and aligns its yielded control and full checked state with public `AllocatedNativeMuSource.enter_prefix`. Unsupported identity cases cannot reach an optional site. The exact final site is then split by official `NativeOptionalPrefix.bound_optional_cases`. The completed child's actual continuation suffix is forced to zero steps; it is not matched by payload alone.

This is a LOCAL compiler classifier. The supplied request is not proved to be a captured memo owner or an original program source request. No owner handle, initial Good/Fields/History, final-site Inputs, or site-body Available is claimed or assumed. The prefix does not include execution of the final instruction. Original binding ancestry and global renewal remain separate.

Validation: selected strict `mu-prefix-direct-3` returned zero and its raw log is empty. Selected `mu-prefix-public-1` was personally polled to terminal zero and prints the complete explicit public statement, proof, and axiom report with all eight printer settings. Only `propext`, `Classical.choice`, and `Quot.sound` occur in its axiom report. Every actual job uses pinned Lean and all linters under a verified five-minute cap with 4 GiB MemoryMax/MemoryHigh and zero swap. Fresh usage gates and inner cgroup readbacks are retained.

Counts: one generic public theorem, zero constructed heads, four actual Lean jobs, two preserved elaboration failures, and zero owned canonical jobs. Failure 1 required exposing the literal entered control before dependent trace inversion. Failure 2 required reflexive proofs for two identities already rewritten by their case splits. No mathematical contract changed. No repository or canonical file was changed. All earlier frozen components remain unchanged.
