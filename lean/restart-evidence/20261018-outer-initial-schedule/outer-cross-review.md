# Independent outer schedule and edge adapter review

Reviewed the full frozen sources and their selected imported proof output. No material issue was found. This review adds no Lean declaration, build, or public pair. It reuses the 17 schedule pairs and two edge adapter pairs.

## Exact phase schedule

`OuterInitialSchedule` uses only outer fuel, local query budget, initial finite raw alphabet, and initial numeric profile. Its row successor orders Parent, returned-edge descendants, then the original suffix. Its walk successor orders the selected node demand, then the original suffix at the predicted node return. The ordinary body runs rows at predecessor fuel and then one raw node constructor. Descendants run the unchanged-heap equality prefix, their same-fuel children, then one raw edge constructor. These orders match the literal `AllocatedPartialWorker` equations.

At zero fuel, ordinary nonempty row and walk executions cannot return successfully. Empty rows and walks retain their entry. Empty, explicit union, and available filtered Mu node-body branches can succeed with zero fuel and unchanged checked state. The schedule therefore uses its entry for body zero. Descendants still reserve a raw edge at zero: contradiction can erase all slots and an empty live child walk can return without recursion. This is intentional padding.

Node ready hits bypass the scheduled body. Edge ready hits bypass Parent. Contradictory child calls bypass the scheduled walk. The six `*_ge` proofs retain initial profile and alphabet on these paths. The private induction uses composition at the exact predicted intermediate pairs. It does not require either alphabet or profile monotonicity of the schedule. It does not choose a schedule by inspecting a future state.

`parent_reserved` reduces Room at the predicted Parent output to Room at its finite common class profile by `MkEdgeNumeric.finalProfile_ge`. `ParentInitialRoom.uniform_of_room` then covers every exact initial own-record image, count through initial mass, and ordered ambient guard word through the initial edge count. Each class case derives its Scan and continuation reservations. This is a pure initial finite case enumeration. It does not assert a concrete host word width, and Room alone does not supply a semantic Context or Frame.

## Captured owners and exact endpoints

`OuterEdgeGuardAlphabet.body_complete` constructs the full old EdgeBodyNumeric receipt and independently constructs the uniform Parent return from the same initial caller. It runs both at the maximum of their lower thresholds. Successful-return uniqueness equates the whole caller state, including checked state, fourth memo, Merge, and both outer tables. Only numeric Fits and the raw alphabet law are transferred from the second construction. The first receipt retains its own exact returned inventory and logical global memo bundle. No equality of independent logical inventories or bundles is assumed.

`edge_body` aligns an arbitrary literal successful observation by the same full-state uniqueness. No observed lower-fuel threshold is a premise. In `edge_call`, the ready branch uses the initial semantic memo law and preserves the exact full caller. Its conservative common profile and alphabet contain the entry. The evaluating branch obtains the captured original owner, owner input residency, and inherited readiness from `CallSteps.edge_start`. It transports Frame, Fits, and carrier across the literal unchanged checked state. It executes the captured original, not a substituted later requester. The old evaluated receipt protects and finishes the same edge handle. Its semantic receipt also retains the independent node result family. Full endpoint equality transports the carrier and Fits through finish, whose checked state is unchanged. Busy and absent branches contradict the supplied successful observation.

The initial Context, Frame, Fits, resident edge, inherited readiness, known alphabet, and uniform reservation remain explicit. Weak physical Good alone is insufficient for a warm result language law. The adapter neither repairs arbitrary malformed result tables nor infers semantic validity from a raw hit.

## Evidence and remaining boundary

Pinned schedule SHA d601b3b8c8171b1ea38d9b6adb2651b92e350927ea46307bdca5a1ddc4a16046 and edge adapter SHA aa5f16941629c4f82f6cfa36229d9eb2abdbdf3fde4078819ff269ef957a117c. Selected strict logs are schedule direct-3 and edge direct-1, both zero bytes. Their canonical-1 runs terminate successfully. Both selected public-1 groups have complete signature, proof, and axiom output, all eight explicit options, and only permitted standard axioms. Canonical replay warnings from older dependencies do not occur in the selected own-source strict logs.

The pure schedule alone does not establish actual output bounds for all six workers. The separate mutual observed-success proof must still compose each phase's Context, Frame, Fits, carrier, and Post. This review does not claim arbitrary fixed-fuel success, all-active-ancestor exclusion, unbounded outer completion, convergence, or Haskell runtime correspondence. It does not review the unfinished mutual producer.
