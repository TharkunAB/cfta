[2026-11-19 04:01 CET] Causal compatibility: checked components and one bounded diagnostic

Source80 remains the strongest published theorem. For each emitted output of
the accepted first-order source pipeline, one finite assignment satisfies the
current native state, union-find state, and stored guards. The same assignment
completes every successful partial-root readback of that output. The theorem
retains the same original source, build, root, initialization, fuel, depth, and
eager execution. It does not establish that an output or readback exists.
Source80 code is fba6e8c66971245ae3ca6bce12bacefc898e22f6. Its checkpoint is
6817cf4bdc2279d764cdc3f52f3a7c353b104b23. Both are pushed to origin/formalize.

The largest soundness gap is one compatible finite assignment for the current
state and all causal constraints removed or parked earlier in the run. Separate
assignments for separate groups do not prove compatibility. Acceptance of the
same original emitted root needs that compatibility and causal transport.
Completeness and correspondence with compiled Haskell remain open. The full
objective also retains typing, preprocessing and LPO, output order and
multiplicity, laziness, counts, weights, training, ranking inverses, and host
bounds. No claim in this checkpoint removes those obligations.

The fresh-instantiation occurs diagnostic completed. The library has
sink :: a -> Bool, t :: (a -> a) -> a, and i :: a -> a. GHC accepts the positive
control sink (t i). It rejects sink (t t) at its exact application because a
finite type cannot satisfy a = a -> a. The public enumeration exhausted 45
outputs. The typed enumeration exhausted 56 outputs. Each run contains the
positive candidate and excludes the negative candidate. The runs are separate;
their outputs are not joined by position. The typed positive output has an empty
residual list. Its type fields still contain Mu placeholders. That printed
output is not a finite-type certificate. Actual repeated-key branch coverage
and proper-path fresh-class coverage were not measured. This diagnostic proves
no general soundness or completeness result and establishes no counterexample.

The original diagnostic supervisor rejected the negative control's diagnostic
format after the expected compile, positive, and negative exits 0, 0, and 1.
GHC used an ASCII opening backtick. The supervisor normalized other quote marks
but omitted that one. The original failed receipt is retained. The already
compiled diagnostic was then run under the same serial 4 GiB, zero-swap cap.
The runtime exited 0. A separate supervisor repair adds only backtick
normalization and its own paths. Static replay accepts the saved negative log
and does not classify the saved positive log as negative. That successor has
not rerun GHC or the diagnostic. This is a Python diagnostic-classifier fix.
No Haskell implementation defect or fix was established. No production Haskell
file changed. Record any future Haskell fix in root FINDINGS.md.

Two small private proof components passed Lean. The terminal-join component
uses the actual preparation and selected child. It proves that inherited and
fresh constraints on the same terminal child path end in one union-find class.
Its terminal-before state remains arbitrary and total; the statement does not
add a causal connection to that state. The ordinary-union component proves that
every union record after makeUnion of ordinary roots existed at the same key
before the call. An earlier failed proof attempt is retained with zero credit.
The repair unfolds run/nodeStep before it applies the existing record lemma.
Each successful component has one exact private axiom report, only standard
Lean axioms, zero warnings or errors, and no compiler object output. These
components are not normal-source additions or a new end-to-end theorem.

The proposed next invariant excludes union records from the current heap.
Source initialization, stored substitution, actual intersection, and warm
execution all need preservation proofs. The restricted constructor induction
and its stored-encoder connection are OPEN drafts at this cut. No result for
these drafts is included here. Even successful no-union preservation will not
by itself prove compatibility of all historical constraints. Repeated-key
clearing can bypass the terminal union step. Its causal origin proof remains
necessary. A broader proposed shortcut, that every Type row has full top
constraints, is false: generalizing a -> a adds an equality class. Existing
source laws do establish full top constraints on the stored universe body.
That distinction is intentional Haskell behavior, not a Haskell defect.

Cleanup removed the exact inactive diagnostic directory
/tmp/mcfta-source-fresh-occurs-rmba6z28: six regular files, 10881163 bytes.
The preserved source/toolchain inventory has 6302 files. The normal cache has
6332 targets. Their fingerprints are unchanged. Unknown temporary files were
preserved. Protected process-inspection errors are retained; complete process
visibility is not claimed. The diagnostic source, commands, full logs, failure,
runtime result, quote repair, and cleanup result are retained in the archive.
Compiled binaries and objects are excluded. They can be rebuilt from source.

Primary usage was 48 percent at 2026-11-19T02:51:24.120Z. Pause and notify Matti
if a current measured reading exceeds 80 percent. The goal control still
reports paused. Matti's explicit resume authorizes manual work. No goal status
change or goal-completion claim is made. The authorized push destination is
git@github.com:TharkunAB/cfta.git, refs/heads/formalize.
