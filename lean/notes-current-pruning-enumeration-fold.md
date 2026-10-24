# Ordered checked pending-slot assimilation

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `a90eeedd3ca92d315cc59989f0693efc88d5bba9`.

The suffix processes the original ordered list of recorded representatives.
It retains duplicates and the winner. Earlier occurrences can make later
occurrences equal-ID or eliminated-source no-ops. It does not deduplicate.
For the native terminal caller, the starting endpoint must come from the
observed representative, union, winner-read and count-transfer prefix.
This component does not construct or identify that prefix by itself.
It also does not merge the real incoming node after the suffix.

run uses the existing Dispatch result and existing list of enum Except rows.
No new result carrier or shared native/enumeration monad is introduced.
Each reached occurrence computes dispatch once and executes its captured
action once at the current enumeration state. Only the exact successful
singleton continues with the next occurrence. An empty list rejects.
Enum errors, mixed or multiple rows and other raw results remain unchanged.
No later occurrence runs after that raw result.

Native Demand and worker interruptions remain distinct from enum raw results
and from absent optional actions. The returned Caller and query pair retain
the reached native effects. The outer enum field is the last completed prefix
state. A rejected head can change the native endpoint while leaving this enum
state at the head's entry. Controls and faults are retained; returning them
does not implement whole-fold resume or restore earlier native state.

Ranges is one source-specific recursive Prop. It requires the actual head's
conditional decoded-pair WordRanges. Tail obligations use universal
implications from literal computed dispatch and raw-singleton equations.
These implications do not assume that a successful transition exists.
The finite theorem constructs the transitions from genuine input Context,
all-slot PendingRealized, an actual pending target and selected source slots
that are pending or eliminated. Context alone does not supply WordRanges.
No successful query, action, fold, callback law or desired endpoint is assumed.

run_complete derives common native and independent worker bounds, stable
under larger supplied bounds. It threads the actual Caller and query pair,
next inventory and logical memo bundle through Post.context and Post.trans.
The result includes full Post, final.query equality and all-slot realization.
The raw result is rejection or the exact completed singleton. Completion
retains a pending target and eliminates processed non-target sources.
Earlier eliminated slots remain eliminated. Values length, representatives,
counter, obligations and expansionAncestry stay unchanged; recursionAncestry
stays unchanged away from the target. No full compression Frame is claimed.

Rejection includes an actual first-rejection witness. It splits the original
list into a successful prefix, rejecting occurrence and unprocessed suffix.
The same global bounds produce the exact prefix Caller, enum state and query
pair, then the literal head dispatch and empty action result. The final enum
state equals that prefix state. Generic successful-observation retention
alone cannot establish this rejection result. No completed fold is invented.

The first strict input failed because the public binder prefix is a reserved Lean token. V2 quotes that identifier. The second input failed at an implicit slot-index type and three default-heartbeat limits. V3 states the existing Nat index type explicitly in three contracts. The third input failed at an equality substitution and two rewrites inside an unreduced tuple match. The fourth input reverses that equality and reduces the tuple before each rewrite. It passes with a literal empty log under all linters and warnings as errors. All three failed sources, complete raw outputs and exact patches remain. V1/V2 owners and reviews remain immutable. The changes add no premise and change no mathematical result or proof limit. The source has 353 ordinary lines, within the soft estimate and hard cap. The installed build, complete public readback and Audit pass. All 126 public-output lines retain three complete signatures without display omissions. No passing check was repeated. Separate read-only metadata comparison diagnostics remain recorded; they are not Lean or seal attempts.
The installed build passes 1293 jobs. Audit passes 3705 jobs and
76258 dependency checks, with the unchanged older warning.
run, Ranges and run_complete each report exactly propext, Classical.choice and Quot.sound. No project axiom is added.

The selected interface has run, Ranges and run_complete. It uses one list
induction and the necessary recursive range proposition. It adds no instance,
helper theorem, datatype or carrier. The soft source estimate is 320–460
lines and the hard cap is 600. The rejection witness, common bounds and exact
state frames extend the earlier prospective 200–320 estimate.
No current compiler result or source-line total is predicted by that estimate.

Native root-flag provenance, representative/union/count-prefix construction,
waiting/candidate indexes, host containers, finite-width extraction, incoming
node merging, code generation and whole-driver correspondence remain separate.
H6 stays strongest combined: covered closed construction with valid initial
caches and allocation history supports any prescribed finite number of modeled
node-reduction calls at derived sufficient mathematical width and fuels.
The empty inherited payload preserves exact finite-tree language. All-producer
origins/edits, cutoff language and full typing/pruning/runtime/solver/resource/
convergence claims remain open. H23, older proofs and the optimized core remain.
No Haskell source changes. Six repair handoffs remain first in FINDINGS.
All 26 prior custody inputs and the already sealed next-assessment review remain.
The whole goal stays ACTIVE and incomplete. This record precedes evidence and push.
