# Independent recursive prefix induction review

Reviewed at 2026-10-17 01:15 CEST. No material defect was found. No production file changed.

The review covers `SourceCurrentAllocatedRecursivePrefixInduction` and its actual
caller `SourceCurrentAllocatedRecursivePrefixAdmission.prefixes`. It also checks
the receipt, protected-body split, current-state, and local compiler certificates.
The manifest records the exact reviewed source bytes.

`Admits` quantifies supplied actual raw `Steps`. It concludes a physical receipt
for those same controls and full checked states. The three helper theorems retain
an explicit callback for counts strictly below `bound`. They do not prove the
whole induction themselves. The separately imported `Admission.prefixes` closes
that callback by strong induction under fixed-source and initial-domain resources.

The decrease is strict. Each main successor branch first consumes its actual
request or edge-body yield. It then calls a helper with `bound = fuel + 1` and
remaining length `fuel`. Inside-body recursion uses this shorter length. In a
crossed body, both counts are at most that shorter length. A consumed finish
reduces the remaining continuation length again. No helper invokes the callback
at `bound`.

The physical body post precedes owner publication. The smaller body receipt ends
at its literal pure result. `body.result` derives `Available` or `EdgeResident` at
the same returned machine. The raw protected-body theorem retains the captured
request and handle. These facts supply the finish instruction's physical Inputs.
The code then applies the actual one-step state theorem. It transports the value
through that finish extension before certifying the outer continuation. It does
not obtain the body post from the desired final result or a future completion law.

State joins are exact. The crossed receipt ends at the `middle` checked state.
Its finish updates only that state's native component. Its equality operations
are the operations returned by the actual body. The continuation starts at that
exact full state. `Receipt.join` composes the actual physical traces, machine
extension, heap retention, and operations growth. It does not replace the return
with an existential endpoint from a separate execution.

Field checks grow along the actual operations relation. Initial continuation
fields pass through the body operations growth. The literal finish receives those
fields. Its derived outcome fields then pass to the smaller continuation call.
A stopped finish frame already has the exact running owner and physical result;
it does not claim that the finish has executed.

An unfinished body permits an arbitrary outer output post only because its
wrapped control cannot equal a pure result. `bind_inside` proves this fact from
an explicit nonpure premise. This vacuity cannot certify a returned pure value.
The third independent kernel checks that case with the outer post `False`.

Validation:

- The focused canonical Induction build passed with 1131 jobs. The Admission
  build passed with 1134 jobs. Their owned log copies retain only the historical
  unused-variable warning from `InternedFreshOrdinaryClosedCompletion.lean`.
- `induction-review-public-2.log` passed four imported axiom and full-signature
  pairs: `Admits`, `bind`, `node_bind`, and `edge_bind`.
- `induction-review-kernels-4.log` passed three imported integration pairs with
  all linters and explicit proof, universe, and deep-term output enabled.
  No warning, error, `sorryAx`, or output truncation appears in either final
  probe log. Failed kernel drafts and raw logs remain unchanged.
- `induction-review-source-1.log` passed a direct source check with all linters.
  The final probes use the canonical dependencies after the ProtectedPrefix
  instance cleanup. That cleanup changes no proof body. The owned final Audit
  log records 2711 jobs and 61656 dependency checks. It has only the same
  historical dependency warning. Earlier focused build copies remain as
  historical validation. The final current-source hashes appear in the manifest.
- The node and edge kernels start from source resources, current initial facts,
  actual operand scope and readiness, an exact running owner, and a supplied
  raw body trace. They derive the compiler certificate and natural body post.
  They append one literal finish and prove a full receipt, physical returned
  result, exact returned owner cell, and unchanged body equality operations.
  `Admission.prefixes` supplies all smaller-prefix callbacks. No external IH,
  physical trace, word plan, or desired body-post premise appears in their types.
- The unfinished-node kernel derives its own body receipt and proves that the
  wrapped prefix has no pure output. It claims no body completion.

The reviewed Admission theorem derives checks for each supplied finite yielded
prefix under its stated initial source and domain-supply conditions. This result
does not prove termination, arbitrary native success, whole-library source
correspondence, GHC scheduling or machine arithmetic correspondence. The resource
predicate still requires a valid initial domain cache, source node and edge key
bounds, and sufficient domain identity space for its explicit finite inventory.
A coarse inventory can make that last bound impractical. These conditions must
remain visible in later endpoints.
