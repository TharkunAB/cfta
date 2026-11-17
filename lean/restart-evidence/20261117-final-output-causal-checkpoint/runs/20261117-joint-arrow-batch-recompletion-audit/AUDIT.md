# Joint finite arrow assignments need more than individual bucket witnesses

Status: mathematical and source-interface audit. No new theorem was compiled. No accepted-source counterexample is claimed. The original joint source objective is unchanged.

## Answer

A finite family of individually typed and compatible arrow buckets need not have a joint finite assignment. A two-owner proper cycle is enough. Even an acyclic graph of raw owner-to-target edges can fail after equal-position requirements identify targets. The ordering must therefore respect the final UF and the equalities induced by the constraints.

A valid small positive theorem is possible for an independent finite batch. Use one dependency-closed kept set that contains every raw target and excludes every owner class. Require pairwise distinct owner classes. The exact proposed header is frozen separately. It reuses the existing one-bucket theorem and assumes no joint assignment, model, historical Holds or future result. These generic independence premises are not asserted for actual source histories.

## Mathematical boundary 1: two owners

Let a and b be distinct UF roots. Each removed bucket contains one target with trie path [1]:

    a at [1] = b
    b at [1] = a

Take the initial assignment constant var1. Every target is TypeIn for any source catalog. Each bucket has only one target at its position, so local compatibility is trivial. Each owner is separate from its own target. Each one-bucket theorem therefore has its own witness.

Any joint finite assignment would satisfy height(rho b) < height(rho a) and height(rho a) < height(rho b), a contradiction. `Language.atPath_height_bound` and the existing `Recursion.proper_closed_references_no_assignment` implement the same finite-height argument. If all target values also had to remain their initial var1 values, even more constraints would fail. The contradiction above does not require freezing those values.

Patching a first with arrow(var1,var1), then b with arrow(rho a,var1), breaks the first obligation. Recomputing stored fragment equations does not recompute removed buckets. A snapshot with only cleared pending owners may be Safe and Stratified; neither snapshot condition records these removed constraints.

## Mathematical boundary 2: raw DAG is insufficient

Use two owners a,b and a third raw target c:

    a at [1] = b
    a at [1] = c
    b at [1] = c

The raw graph a→b, a→c, b→c is acyclic. Constant var1 again makes every target TypeIn and each bucket locally compatible. Each owner avoids its own raw targets. A joint assignment must first satisfy rho b = rho c, since both occupy the same child of a. The last constraint requires height(rho c) < height(rho b), a contradiction.

After quotienting by the required equality b=c, the apparent DAG contains a proper self-cycle. This is a mathematical refutation of raw-DAG sufficiency. It is not an execution trace, an accepted source example or a Haskell defect.

## Positive batch proof path

Induct on `events`. Keep the final enum state, roots and stratification fixed. The empty list uses the original current assignment, with the stored-equation orientation reversed as required.

For head event, apply `recomplete_arrow_bucket_at_snapshot` with the common kept set. Its result preserves every target in every event because all targets belong to that same set. Transport each tail target's TypeIn and equality premises through this agreement. Apply the induction hypothesis to the tail with the new current assignment.

The tail result preserves the head owner's term: the head is still a pending slot in the fixed state, and pairwise distinct owner classes place it outside every tail owner class. Its target terms are also preserved by common kept agreement. The head's arrow shape and Holds clauses therefore remain true. The induction result supplies all stored equations at once. Compose both outside-pending equalities for the final clause.

No witness is selected independently and spliced later. The proof constructs a single assignment through the finite induction. No actual source theorem is replaced by this restricted independent-batch statement.

## Why current receipts do not yet prove this for every actual event

`ExpandedBirthHistory` protects already expanded classes and records origins of later expanded fragments. `ExpandedBirthKept` uses those receipts and held isolation to close a kept set for ONE held owner. Its definition explicitly excludes that owner class, not every historical owner. A raw target of an earlier clear can be a later clear's owner; that target must change when the later owner receives its own arrow. Thus the union of all one-event target sets need not satisfy the independent-batch header.

`EnumerationOrder.Stratified` orders only currently stored fragments. All current pending roots share frontier, and removed buckets do not occur in its expanded field. It cannot alone rank the historical owner→target edges.

`HeldFragmentHistory.isolated` and `.protectedHeld` are promising stronger actual facts. Once an earlier clear has created an isolated held owner, `IsolatedPending.incoming` excludes incoming suspended references to it at every later state where the certificate is preserved. A later actual stored bucket therefore cannot target that earlier held class. `HeldFragmentHistory.origin` also excludes later-born expanded dependencies on it. These receipts can support reverse chronological recompletion, but only after the actual event, bucket occurrence and final raw aliases have been attached to the SAME causal output. No relationship between independently selected local receipts is assumed here.

The existing `selected_clear_proper_cycle_unsatisfiable` already shows that an actual selected clear cannot erase a proper cycle present in one current stored dependency set. It does not by itself combine buckets that were removed at different earlier points. The selection premise is important; the mathematical examples above do not supply it.

## Next authentic source step

First attach all relevant earlier clear events to one output branch, with indexed original owners/targets and actual alias transport. Retain the actual clear order. Derive an order on FINAL UF classes for both historical proper-path edges and stored-fragment hole edges. Equal-position targets must be actual final aliases, so this order is also valid after their congruence identifications. A raw-slot order alone is insufficient.

Recomplete in reverse causal order. At each patch, keep every already repaired owner and its dependency closure, including that owner's raw targets. Derive their separation from the current held owner using the actual isolation/protection/origin suffix. The next patch then preserves previously established Holds rather than merely preserving current equations.

Target typing must also survive this sequence. Typing under only the original canonical var1-based assignment is not yet the complete induction invariant if another owner or an expanded dependency changes. The source Type-role producer should support reconstruction under the new typed pending choices, or the patch step must prove that its typed targets remain unchanged. This is a concrete strengthening to check in the next target-typing work; it is not a new top-level source premise.

Native-domain and retained-guard satisfaction still need their own same-assignment preservation. An arrow TypeIn term belongs to original U, but not automatically to an arbitrary narrowed domain. Neither this batch theorem nor a proper-dependency rank proves the full joint source model.
