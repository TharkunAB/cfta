# Correct public clear theorem namespace

Root strict59881 has one remaining primary diagnostic at269. The proof already imports MicroCFTA.SourcePruningEnumerationParkedLanguage explicitly at line5. The theorem is declared in MicroCFTA.SourcePruningEnumerationRecursion, not the namespace suggested by its file name.

This repair replaces ONLY the TWO proof uses of SourcePruningEnumerationParkedLanguage.clear_satisfies with SourcePruningEnumerationRecursion.clear_satisfies. The second use is the retained-guard specialization of the same actual clear. The complete public header7f265de2, declarationc869b887, preamble, imports, probes554593b6 and every other source byte remain exact. No extra import or alias is added.

The old raw/index/frame/first packets and all Root logs remain immutable. No earlier failed packet receives theorem credit. Status: UNCOMPILED. No Source, compiler, Git, board, root document, tmp, Haskell, budget or warning change is made.
