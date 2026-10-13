# Proper source equality paths

`EqualityLeafProjectionProperPaths.normalized_proper` derives nonempty
selected paths from completed source normalization. The proof uses only
nontrivial output classes and the strict-prefix contradiction check. It
does not assume a satisfying finite term. Reordering and filtering output
classes preserve the property. `array_eventual_proper` connects the result
to the executable source array normalizer at sufficient work bounds.

The public `EqConstraints` pattern can directly intern a caller-supplied
class list. It does not normalize that list. Therefore the property applies
to completed `mkEqConstraints` output and lists with its established
invariants. It is not a property of every arbitrary public raw constructor
value. The projected runtime fragment must retain this boundary.

The source `setChildren` in `Data.CFTA.Interned.Type` directly interns the
replacement when child arity is unchanged. Its checked `mkEdge` branch runs
only when arity changes. Simultaneous leaf editing and required-path child
traversal preserve each surviving row's child count. Consequently ancestor
reconstruction uses the direct interning branch with the original full
constraint, including its residual guard syntax. Parent normalization may
remove a row after a child becomes empty.
