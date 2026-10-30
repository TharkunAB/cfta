# Conditional native cache preservation through mixed calls

Source: `4adf96c3fdd959a255c4b888bd40bd65b0822588` on `formalize`.
Main at this checkpoint: `bd5a406a6a3f84b7e3ae0906082783911509df83`.
The full original-input objective remains incomplete. Work continues.

## Checked result

Six laws in SourceCurrentAllocatedNativeStoredTrace preserve the existing
conditional finite ordinary property of native returned memo cells.

| Law | Result |
| --- | --- |
| clean_trace_stored | Preserve Stored through an actual completed Clean physical Trace. |
| node_trace_stored | Preserve Stored through a literal node request. Derive Fields and Clean internally. |
| edge_trace_stored | Preserve Stored through a literal edge request. Derive Fields and Clean internally. |
| node_receipt_stored | Use the existing actual node Receipt and its own Trace. |
| edge_receipt_stored | Use the existing actual edge Receipt and its own Trace. |
| initial_clean_trace_stored | Derive entry Stored internally at literal PartialInitialization.checked. |

Stored quantifies over returned cells in both native thunk tables. If a
cell's own stored request has empty seen and both operands belong recursively
to the finite ordinary domain, its result belongs to that domain. Its height
is at most each operand's height. The edge law uses complete child forests.
This domain excludes Mu, explicit union and reference records at every
level. An ordinary root alone does not establish domain membership.
The certificate imposes no result bound when an antecedent fails.

The generic law retains Good, SemanticReady, Fields, entry Stored and Clean.
Literal request laws construct Fields and Clean. Their other entry gates
remain. Receipt laws use the arbitrary existing Receipt's trace field.
They need no new result postcondition. The initial companion removes Stored
at the existing literal initializer. It retains the other entry gates.
The supplied equality cache need not be empty. The native thunk tables start
empty at that initializer.

Trace is the existing checked physical trace. Each step includes its Inputs
witness and the literal step equation. These laws consume a completed trace
or its existing Receipt. They do not derive that trace from an arbitrary
execute equation. They do not establish future completion.

## Actual proof

The proof reuses BodyCode and Clean. It follows the actual work, scope entry,
read, optional binder, direct node bypass, cache hit and cold owner branches.
It isolates each actual cold body and its finish with bind_inverse.
If that owner's finite ordinary inputs hold, the existing verified theorem
proves its real certificate. Otherwise the smaller-fuel Clean induction
preserves Stored and the conditional owner certificate is vacuous.
A recursive parent can contain an ordinary nested owner. Each owner gets
its own branch. No proof treats all nested certificates as vacuous.
Frames retain the exact evaluating owner through its actual body. The
literal finish publishes the proved certificate at that same owner.

This removes the need for a caller-supplied mixed-body verifier or ordinary
operand-domain assumption in these preservation laws. It introduces no new
cache model. Native structural Stored differs from Ready.scopedCache, which
only controls result scope. Context.stored controls a separate merge memo.
Neither predicate is substituted for native Stored.

## Strongest whole-worker result retained

The earlier whole-worker source and all nine original-carrier laws remain
exact. For each supplied finite recursive depth satisfying the existing
input/resource gates, both actual workers have a stable outcome with exact
computed resources and paths in one original finite carrier. The final laws
discharge Complete and the smaller-depth path induction internally.
The path carrier is independent of depth. Work bounds, forecasts and Reserved
can depend on depth. Fixed-depth recursive exhaustion remains permitted.
No common successful outcome across all depths is established.
The three successful recording control laws remain exact too.

## Remaining gaps

The new native result covers completed calls. Transport through EnabledEmpty,
every caller writer and whole-worker composition still needs proof. Arbitrary
yielded, failed or blocked prefixes do not receive a new Stored theorem here.
The finite ordinary return theorem still needs both recursive operand domains
and WordRanges. The new cache invariant does not establish those inputs.

The largest gap remains sufficient ORIGINAL recursive capacity for the
intended finite ordered prefix, with the configured order and stops. It must
cover every earlier alternative and staged child. Handle changes, neutral
progress, raw SCS multiplicity, slot work and total work still need bounds.
The checked recursive-boundary action retains its physical constructor handle
and consumes a shape for that same handle. The renewal gap lies between such
episodes. RecursionKey erases duplicate shapes but retains the constructor
handle. Shape cardinality does not bound raw bucket work or native allocation.

Action.prepare has a separate nonboundary branch that can install a changed
encoded handle before constructor production. Its actual OuterNarrow primitive
bypasses Mu and known type positions. NativeView.narrowAt filters existing
complete root rows. This primitive does not run recursive native intersection.
A separate source-only review at
/tmp/mcfta-preparation-renewal-measure-review-20261030 checks replay and finite
row-subset control with the real Normal/canonical readback gates. Its work is
not a checked result of this checkpoint. Incoming/dispatch intersections and
Prepared selected Mu/Union reconstruction remain separate operations.
No admitted runtime renewal witness or Haskell defect follows from a potential
write branch.

Keep full public-input validity, output soundness, intended ordered prefix
coverage under sufficient original resources, both workers, the optimized
interned core, Prefix/table/count/checkpoint/public adapters and Haskell
correspondence. Keep constructor/equality, exact node-count size classes,
size order and both rank/unrank inverse goals. No completion percentage is
established.

## Verification and evidence

Default and strict Audit pass: 4,746 jobs and 82,987 dependency checks.
All seven serial compiler commands pass. All 12 input snapshots remain.
The exact installed source matches its strict snapshot. Its strict log is empty.
Lean is 4.34.1 with warningAsError and linter.all. Every command verifies
memory.max/high at 4 GiB, zero swap and the five-minute cap. No resource,
heartbeat, queue or service setting changed. Default Lake replays the existing
unused-input warning.

Public verification passes 1,195 checks and the unchanged 116 definition
prints. All previous 4,837,716 bytes remain an exact prefix. The complete
11,037-byte tail and all six standard-only axiom reports were read against
the source. Full output is 4,848,753 bytes, SHA256
`a6b8e9e53bf02426fcbc6159c5a2a1337cbe6d3c578ca4b7d131674619cc9282`.
All 546 prior protected and 835 native inputs remain exact. There are now
547 protected inputs and 4,746 Lean files. One Audit import precedes the
complete old body.

The frozen source owner retains 169 payloads and 171 regular files. Root
verifies 137 acquisition records over 73 sources. Three old whole modules
were named before reading; Root explicitly approved the third extension.
The independent public review retains 32 payloads and 34 regular files.
It read all 290 source lines and all 166 public-tail lines. It acquired zero
old whole sources. All reports, failed metadata previews, repaired ownership
verifier versions, source-only incidents and original drafts remain.
No compiler check failed. The installed V3 removes only V2's uncompiled
status line. All proof headers and bodies remain exact.

Evidence: /tmp/mcfta-native-memo-stored-control-20261030.
Archive: lean/restart-evidence/20261030-native-memo-stored-control.
Use safe extraction into a fresh destination. Remove restored write bits
before ownership checks. Give metadata verifiers a writable output directory.
All historical report/manifest dependencies are retained within the snapshot.
All prior root documents remain complete exact suffixes.

No Haskell source changed. No native command ran. No new Haskell defect, fix
or repair candidate is established. FINDINGS retains all prior conditional
findings. Public adapters and Haskell Word64, interner, container, laziness
and warm-CAF correspondence remain open. The backend goal marker still says
blocked despite explicit resumed work and verified progress. No pause or
completion is claimed.
