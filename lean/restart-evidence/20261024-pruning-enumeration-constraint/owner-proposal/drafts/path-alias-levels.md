# Prefreeze type-alias correction

The active review metadata uses the actual existing aliases: Path = List Nat, Class = List Path, Constraints = List Class. The first generated review metadata omitted one List level in some classes and paths binder types. The exact literal headers and all local have fragments used inferred existing types and were already correct. They did not change. The three original metadata files are retained here. No body or compiler was used.
