# Completed class prefixes separate a dropped child

The pure geometry is now proved in Lean.
The single module has three public declarations: the relation `Rel` and the theorems `single` and `child_separate`.
It changes no official source.

`Rel classes left right` is a finite chain of equality transfers.
One transfer replaces two recorded paths from the same class and retains their common appended suffix.
The relation also has reflexive and transitive constructors.
Symmetry follows by reversing the transfers.
It is right congruence on position paths.
It is not congruence under a common prepended path.

`single` assumes only the actual executable fixed point `congruenceStep classes = some classes`.
It reduces any `Rel` chain to exact path equality or one class-prefix replacement.
The output exposes the selected class, both exact recorded members, and their common suffix.
It does not assume a property that is equivalent to this conclusion.

To compose replacements, write their shared path as `b ++ s = c ++ t`.
The recorded prefixes b and c are comparable.
If c is b followed by u, fixed-point congruence closure puts every first-class path followed by u in a completed component containing c.
Disjoint component completion identifies that component with the second class.
The composite is therefore one replacement in the second class, with suffix t.
The other prefix direction is symmetric.
An empty u uses shared-path component equality directly.
The proof uses `fixedPoint_congruence_closed`, `congruenceStep_disjoint`, and `components_equal` from `EqualityNormalize`.
It uses only list prefix comparability and append cancellation from the installed Lean library.
No termination or normal-form rewrite theorem is required.

`child_separate` assumes the same actual fixed point and that each completed class has at most one path through index j.
From `Rel classes (j::left) other` and `Rel classes (j::right) other`, it proves `left = right`.
It first composes one chain with the reverse of the other.
The fixed point itself implies consistency.
Consistency excludes a nontrivial replacement with an empty recorded prefix.
Both remaining recorded prefixes must start with j.
The all-drop premise identifies their tails.
Common-suffix cancellation then gives the conclusion.
There is no extra Active, proper-path, semantic, heap, ordering, or rank premise.

This closes only the first proposed lemma in `/tmp/mcfta-selected-copy-support-plan.md`.
That earlier report remains unchanged as a source-only proposal at its recorded time.
The actual support transport through Required, Merge, native queries, warm tables, and the chronological class fold remains unproved.
In particular, this module does not infer a `Rel` witness from a copied value.
It contains no cardinality wrapper, owner theorem, completion claim, or runtime correspondence claim.

Before the Lean proof, one bounded independent Python search checked 4389 raw inputs.
The inputs comprise every partition of proper binary paths of length at most two, and every one-pair or two-pair equation set over proper binary paths of length at most three.
The search found 1758 distinct active consistent fixed points and checked 1782 all-drop child cases.
It checked prefix-transfer paths up to `min(8, maximum recorded length + 3)`.
It also checked that the bounded transfer closure equals one replacement.
No counterexample occurred in that finite domain.
There were no skipped normalization cases.
The Python program is an independent finite reimplementation of the source set operations.
Its output is auxiliary evidence, not a proof of the Lean normalizer or an unbounded claim.

There are three owned Lean commands and one owned Python search command.
Lean direct attempt 1 failed on elaboration and emitted missing constructor documentation warnings.
It is preserved unchanged.
Direct attempt 2 checks the final source and has a literally empty log.
Public attempt 1 prints all three declarations with all eight required options.
Its complete log has 79133 bytes and no omissions.
`Rel` uses no axioms.
Both theorems use only `propext` and `Quot.sound`, within the allowed standard three.
All four commands used effective MemoryMax=MemoryHigh=4 GiB, swap=0, timeout=5m, and fresh usage above one percent.
The component owns no canonical job and no constructed proof pair.
Any official promotion and canonical dependency build belong to the parent.
