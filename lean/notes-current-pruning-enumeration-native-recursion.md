# Selected reads and the native recursion guard

## Current result

Clearing history and indexes: `0e9d54829`.
Native guard, selected completion and Audit import: `b13953d85`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

Original pure selection and initial invariants now derive the actual pending
value read and native recursion check. No successful read or successful check
is supplied. Both steps have sufficient finite bounds and exact results at
every larger bound. The reached cache retains safety, Ready, root paths,
realization, canonical waiting counts and all native expandable flags.
Incoming avoidance follows from original selection. Initial global pending
history persists through both steps.

## Source order and native boundaries

Enumeration.hs:993 reads the selected pending value. A recursive boundary then
reads its representative and ancestry. A repeated key clears the bucket and
restarts selection. A new key continues to narrowing. The repeated branch
calls neither narrowing nor an oracle.

The existing Graph-based checker classifies only Graph.recursive. Native
Interned/Type.hs:608 classifies both Mu and explicit Union as recursive
boundaries. The new Recursion.checkRepeated uses lookupNode and the existing
native recursiveBoundary function. Its order is decode, boundary test,
representative read, ancestry membership and conditional clearing.
The source already has the decoded node. The model obtains it through the
realized handle. A missing handle gives an explicit unresolvedReference error;
the completion premises exclude that error.

This worker does not set expansion ancestry. The later ordinary entry does
that. The selected proof uses only Entry.complete's first-read receipt. It
does not execute or use that theorem's later entry state.

## Exact clearing effects

The new generic clear-history laws retain each incoming-reference predicate
and global pending-reference history. Clearing introduces no reference or
enumerated slot. Existing same-bucket replacement laws remain unchanged.

Clear.complete consumes an actual setValue endpoint at a ready pending root.
It derives a native indexed write at that same endpoint. Gained references
are empty. Lost references are the entire old scs. The count fold maps every
occurrence to its current root before subtraction. Repeated references and
aliases remain counted. CanonicalWaiting.replace_correct proves the final
counts. This is not an unchanged-waiting frame.

The new empty bucket has candidate=false at both Mu and Union boundaries.
The target's expandable flag becomes false. Every other flag remains valid.
The handle remains unchanged and realized. The reached state retains Safe,
Ready, paths, exact counts and pending/incoming history. Ready does not assert
that the target remains expandable.

## Guard completion and selected completion

Recursion.complete derives a representative execution from initial storage
totality. The actual root theorem identifies its result with the ready target.
Its full frame transports values, ancestry, paths and cached invariants to
the exact compressed state.

At a repeated key, the guard's representative result, membership test, plain
clearing write and indexed native write use that same resolved state. The
output retains each equation and disables the selected slot. At a new key,
the output retains the full compression frame, original bucket and both index
tables. A nonboundary value returns false without a representative read.

Recursion.selected_complete derives Ready, incoming avoidance and the actual
pending value from selection at the original cache. It derives the initial
getValue execution and identifies the returned payload through the selected
root theorem. It passes that exact readAfter to Recursion.complete.
It composes the two frames in the false case and retains the real clearing
write in the true case. It never repeats the selection equation at a changed
cache and never assumes a future successful step.

The heap is a fixed parameter throughout this prefix. The worker changes no
native Caller or saved memos. The result covers this prefix's structural and
cache invariants. It does not prove language equivalence for clearing or
whole-loop progress, termination or convergence.

## Verification and approaches retained

The generic history module, both native modules and changed Audit import pass
Lean 4.34.1 with all linters and warnings as errors. Eleven strict attempts
remain in evidence. Six fail. The first history attempt needs the references
namespace qualified. The first native clearing attempt needs its concrete
cached waiting field unfolded. The guard's first attempt uses a reserved
identifier. The next rewrites the input root while identifying the result.
The third needs the ExceptT.run projection reduced for the stable equation.
The fourth passes. The selected extension's first attempt needs the Ready
component of getValue_ready. Its second attempt passes. Strict Audit passes.

Two installed helper builds pass. The aggregate Audit passes with 3756 jobs
and 76730 checked dependencies. Installed public readback checks six
declarations, including the worker. Its full output has 209 lines and 16444
bytes. Its SHA-256 is
`1b06898a3119333fdfca650605429bac8c412f794b8504b997f9d6934dcea220`.
Every axiom set is a subset of propext, Classical.choice and Quot.sound.
The older unused inputs warning remains unchanged. All fifteen checks use
4 GiB heavy-management caps with no swap.

Source review confirms the actual Mu-or-Union guard order, shared compressed
witnesses, full lost-bucket update and absence of an early ancestry update.
All attempted inputs, full raw logs, reports, final sources, cap records and
proof patch remain in restart-evidence/20261025-native-recursion.
Audit adds one import. The old generic checker, narrowing producers and
ordinary workers remain unchanged. H6 and Haskell runtime code are unchanged.
No Haskell defect or repair is found. Root FINDINGS retains the external fix
handoff. No Haskell suite is repeated for these model proofs.

## Next work and strongest claim

Connect the false guard endpoint to the existing native narrowing producer.
The guard can compress representatives. NarrowCache.complete and the combined
NarrowContext.complete currently use entry=readAfter. Their underlying
Action.prepare_pending_complete already accepts Frame readAfter entry.
Expose that genuine frame in the cache and Caller producer. Do not insert a
second value read in place of the source prefix.

Then use the exact narrowed Caller, saved memos and enumeration cache for the
concrete Right callback. recordTypes_inr already makes that callback pure and
retains all metadata. For an ordinary nonterminal result, use
NativeOrdinary.complete. Transport Ready and incoming history from original
selection. Do not call selected_complete again at the narrowed cache.
Numeric Ranges admission must refer to that actual reached Caller/cache.

The true branch retains its exact parked endpoint. Composition with the next
scheduler call remains open. Fragment-hole history, successful extraction,
terminal parents, parent normalization, the later fragment callback and
whole-driver language semantics remain open too.

H6 remains the strongest end-to-end language theorem: covered closed
construction, a valid initial cache, original allocation history and any
prescribed finite budget and modeled node-call rounds derive sufficient
finite bounds and one mathematical width chosen after construction. With
empty inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.
Concrete solvers, physical containers and machine counters, arbitrary Haskell
demand and practical resource bounds remain outside that claim.
