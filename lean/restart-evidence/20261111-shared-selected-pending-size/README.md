# Actual selected-edge work bound

A literal complete shared selected edge satisfies after work + 1 <= before work + the filled parent fragment size. The assignment stays fixed. The only state premise is current counter alignment. Own-class None slots add zero work. The actual child traversal supplies its sum bound and all later alignment facts.

The checker compares every public theorem name and namespace. It treats
own-source warnings as errors. It records the source hash and verifies
that theorem axioms are limited to the standard Lean axioms.

Run under the existing serial 4 GiB heavy-management cap:

```sh
python3 lean/restart-evidence/20261111-shared-selected-pending-size/check.py
```

The work measure counts native witness-tree nodes. It does not count public
Program components. These laws do not establish full driver termination,
general original-input completeness, output order, both signed inverses,
or correspondence with Haskell execution. No production Haskell changes
are included.
