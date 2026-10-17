# Independent callback-child reconstruction

Production: SourceCurrentStoredMuChildLineage.lean
SHA: 6e56b622528238dea87d699bea8be8864b6f1b4e6e12e6b18696e0202c66971e

## Exact proved case

`independent` compares two actual past source calls of the same arbitrary
expression. Fixed lexical captures remain complete records. Varying lexical
slots can use different reference assignments. Both source calls have their
actual Contexts and grow into one coherent initial reader with Ready.
Pure source support has no varying label. Replacement maps need agree only
on fixed names in that source support. The initial raw value is available
in the reader. The first map has available replacements there.

The theorem derives exact raw-value equality from live-input replay. It then
uses the exact free-name support of that raw value to derive agreement of the
replacement maps on every free binding that stored execution reads. Initial
Ready data constructs the first stored call. Repaired execute_congr and actual
warm replay construct the second call at the exact first returned heap. Both
calls return the same complete result. The second call leaves that full heap
unchanged. The theorem also retains the first warm replay, Keeps, result
availability, and the produced local publication History.

No reconstructed output equality, child observation relation, future stored
completion, or future heap is an input. The past raw source calls are explicit
component inputs. They are not new query completion claims. The general
available/Ready premises concern the reader before the new reconstructions.
The source syntax and fixed captured records can contain arbitrary nested
raw or smart Mu values. This result does not use PreparedWithoutMu, noDeep,
a finite cap, whole-heap plainness, or whole-forest closedness.

The support condition selects one independent-child induction case. It is not
asserted for all children of an enclosing retained Mu. It does not discharge
the active-child case. InputExchange already supplies raw-value independence;
this producer adds the actual sequential reconstruction under distinct outer
replacement maps. It derives their agreement from source support, instead of
assuming agreement on the eventual raw result or an Alpha relation.

The source uses the repaired execute_congr in
InternedFreshOrdinaryDependencies. The older theorem with the same short name
in InternedStoredSubstitutionBindings concerns the earlier executor. The first
strict attempt exposed this nominal mismatch. That failed snapshot remains.
The final producer has no ordinary-only restriction.

## Constructed validation

The fixture builds a closed nullary source node first. It then executes a
smart used-Mu source expression twice. One varying outer slot uses ordinary
reference 0 on the first call and reference 9 on the second. The nested binder
body uses its own local argument and a separate fixed reference 42; it does
not use the varying outer slot. The second actual source call starts at the
exact first returned heap. All source Contexts, Ready, availability, and growth
facts are derived from these source calls.

Two different outer maps replace fixed reference 42 with the source-built
leaf. They differ at unrelated reference 55. The theorem constructs the first
stored reconstruction and the exact full-state warm second reconstruction.
The proved result remains a Mu. There is no supplied successful call, expected
result, expected final heap, or output relation in the fixture signature.
The literal computations establish only this concrete fixture. They are not
used as the general proof.

## Remaining coupled induction

An active child can contain the varying outer own reference below an ordinary
or Mu boundary. Its two raw values can therefore differ. Raw InputExchange
cannot equate them. The older comparison theorem requires absence of varying
deep names, so it cannot be applied to this case.

The required induction must quantify compatible outer replacement maps and a
common replacement for the two actual own names. It must construct the actual
sequential stored calls and relate all exposed full guards and ordered child
observations, with physical Empty agreement where a parent constructor drops
rows. The relation must be produced from actual callback source and writer
history. It cannot be a hypothesis about the two returned child values.

A source-syntax step handles ordinary rows and ordered child calls. Union
steps require the proved observational and literal union fusion laws because
physical reconstruction does not commute with every earlier makeUnion
normalization. In the nested binder step, smart erasure can replace a Mu with
an ordinary or reference root. A warm request can select a chronologically
earlier writer whose source syntax differs from the current callback.
The stored Mu induction hypothesis must therefore apply to every selected
past writer under arbitrary compatible outer maps, not only singleton own
replacement. All three actual callback histories precede publication, which
provides the chronological component of a possible induction. That induction
and its active-child candidate law remain unproved.

Existing Alpha and recursive normalized plan relations retain constructors,
ordered union members, and binder flags. They do not derive this missing
Mu-versus-erased-root case from actual callback histories. Equal raw child
Empty tests in StoredMuRetainedAlignment do not imply these nonempty child
relations. No general retained-Mu correspondence or outer termination follows
from the independent case proved here.

## Verification

The selected direct source and constructed checks have truly empty logs.
Every direct attempt executes its immutable numbered source snapshot with
Lean 4.34.1 and linter.all=true. The own canonical target passes 560 jobs.
The public group prints one complete explicit signature, proof, and axiom
report. The constructed group prints one complete explicit signature and
axiom report. Both contain all eight requested options and #check @.
Only propext, Classical.choice, and Quot.sound occur. No omissions or printer
failures occur. Each selected worker reads effective memory.max=4294967296,
memory.high=4294967296, and memory.swap.max=0. Failed attempts remain intact.
