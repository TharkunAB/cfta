[2026-11-14 16:44 CET]

Status: UNCOMPILED. Root owns all validation and publication.

The new module imports the now-checked union induction module. It adds two
public concrete constructor producers and three private fuel-induction steps.
It changes no live file. The original full-closure header and the current
coupled A/M header are copied byte for byte from the previous frozen packet.
Both full headers remain OPEN. This packet contains no placeholder proof.

The two public producers are unconditional on any future recursive result:

* make_edge_atoms_checked proves Checked for actual work(makeEdge symbol
  constraint values). It retains EdgeResident, the literal symbol, constraint,
  and ordered children, plus the supplied original owner atom property. Its
  exact child equality comes from actual makeEdge_fields. This includes hits
  on existing complete records.
* make_node_atoms_checked proves Checked for actual work(makeNode edges).
  It derives available output and owner atoms from actual resident input
  edges. makeNode_atom_origin accounts for dead-row filtering and canonical
  edge selection. It does not assume a product language or a semantic heap.

The three PRIVATE induction steps are explicit auxiliary steps. Their
fuelInduction hypotheses are lower-fuel induction hypotheses, not premises
added to either closed theorem:

* ordered_edge_atoms_of_fuel_induction executes the actual zipped child walk
  at fuel n and the actual conjoined-guard makeEdge. It derives child input
  availability from complete resident edge records. If arities differ, it
  executes the original makeEdge with the empty guard and [.empty]. It does
  not call a child in that branch. It retains Checked validity and Extension
  on success and on failure.
* ordered_node_atoms_of_fuel_induction executes the actual occurrence-ordered
  pairs hash join. It composes the actual edge steps in their returned caches,
  then actual work(makeNode values). pairs_member establishes only membership
  for input residency. It does not replace, deduplicate, or reorder the walk.
* ordinary_closed_nodes_atoms_of_fuel_induction proves the actual selected
  ordinary branch of execute(n+1). It derives physical row residency from the
  actual node records. For each zipped child pair, it reuses the checked
  node_child_closed_atoms law on those same parents. It transports the
  available children to the actual later call state, and invokes its explicit
  lower-fuel hypothesis with their closedness and owner atoms. All constructor
  and child effects remain the original operational computations.

Both operand orders are retained by the ordered left/right arguments. The
ordinary branch has the exact actual decision = .ordinary premise. It cannot
bypass union priority, empty/reset/self/swap checks, or any unsupported shape.
The node and edge helpers retain the caller's exact domain at every request.
They can therefore be used at an actual later Extension of original entered
U/P without a new domain entry: instantiate state with that later machine,
keep original entered.1 as domain, and compose the original Extension with
currentInput.1 before applying the mixed induction hypothesis. Domain.grows
transports its existing Domain proof through the ordered effects. No second
source build, body provider, result provider, or new original U is chosen.

For the closed A branch, instantiate domain with emptyDomain and ownerId with
the SAME original stored entry.identity. The existing checked source
boundary_atoms_closed_after_growth law derives output closedness from this
available output and its owner atoms, after composing actual heap growth.
The existing generic node helper also permits an open stored body on one
side, but its local child hypothesis must then be discharged by the actual
coupled mixed induction cases. The closed-parent wrapper does not pretend
that an open stored body has closed children.

Still OPEN: the simultaneous source A/M induction, mixed stored-body child
classification and cutoffs, outer Mu construction, and the remaining native
control cases. The full original generated-type closure and finite accepted
same-original-root witness with one consistent assignment and parked
recompletion are not proved here. All typing, language, LPO, stream, count,
weight, rank, and compiled-Haskell obligations remain separate and unchanged.

Root should probe both public declarations and all three private declarations
inside this module, then run its normal strict checks. No compiler, Nix,
Lake, heavy job, live write, Git write, board post, or child agent ran here.
