# Fun arities omitted from the type universe

The parser accepts Fun/0 and Fun/3 as ordinary constructor types. Public
FirstOrder synthesis fails to return f x for either result type at size 2,
with f : A -> result and x : A. The literal raw-language term is also rejected.
An ordinary Z result and the documented Fun/2 arrow alias both return f x.
A rigid Fun/0 leaf query returns x at size 1. The failure is positional.
No case times out. The exact output is in expected.txt.

Owned source: Synthesis.hs constructorsOf excludes the literal name Fun at every
arity. typeNodeWith treats only Fun/2 as an arrow. Applications require their
result annotation from typesOf. The other Fun arities therefore disappear from
that application-result universe. See root FINDINGS.md for repair requirements.
No production repair is applied. A successful check reproduces this defect.
The runtime claim covers explicit FirstOrder encoding only.

Run from any directory under the established serial 4 GiB cap:

```sh
python3 /path/to/mcfta/lean/restart-evidence/20261112-fun-arity-universe/check.py
```

The checker uses the project Nix/GMP shell, checks probe formatting, verifies six
owned Haskell source snapshots, builds only the generator library offline with
-j1, runs the probe and compares its full output. checked.json records effective
cgroup limits. The packet contains source and metadata, not binary archives.
