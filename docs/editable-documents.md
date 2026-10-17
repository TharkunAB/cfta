# Editable language documents

Preserve the source graph before constraint compilation. Give each transition a
name that is unique within its state. Its annotation holds a map from fact names
to complete constraints. The state and transition name select a production even
when another production is inserted before it. A symbol still identifies its
complete text and refinement. A separate portable constructor schema remains
future work.

Add `Data.CFTA.Document` in the core package. A checked `Document state` contains
an explicit graph over `Symbol` with named source annotations. `mkDocument`
checks graph structure, duplicate state rows, and duplicate transition names.
`fromGraph` gives each imported transition a local name and stores its existing
constraint as one combined fact. It cannot recover the original source facts.
`compileGraph` conjoins the current facts of each transition and retains all
rows, including rows whose constraints are false. It does not invoke a solver.

A patch records its starting document and an ordered list of edits. The edits
replace or delete rows, or set or remove one fact at a named production. Setting
a fact can add it or replace its body. Removing an absent fact reports an error.
Fact edits require their target to exist at that point in the edit sequence.
Row edits can temporarily leave references incomplete; validate the whole
result after the complete batch. The initial state remains fixed.

`applyPatch` first compares the current document with the recorded starting
document. A mismatch reports a stale patch. This is an exact content check,
including names and facts. It does not use a caller-maintained revision counter.
The patch shares its starting value in memory. It is not a compact change-log
format. Undo uses the retained starting document. The first implementation
validates and rebuilds the explicit graph; measure its cost before introducing
incremental indexes or a document digest.

Add a `cfta-document` version 1 encoding to the optional serialization package.
It shares the graph, symbol, formula, and constraint codecs with graph snapshots.
A transition stores `name` and `facts` in place of the compiled `constraint`.
The fact object maps names to full constraints. Duplicate JSON keys remain
errors. A document round trip must retain names, individual facts, order, and
the complete graph. Graph and document formats are distinct and reject each
other's format tag. Query plans, cursors, and patches are not part of this file.

Provide a complete workflow that creates named facts, saves and reopens the
source document, changes facts and constructor rows, compiles the new graph,
and compares its accepted terms. Include removal of a false fact that restores
a branch and removal of one equality fact while retaining another. Exercise
stale patches, invalid atomic batches, duplicate names, and unchanged old
versions. Compare results with independent bounded acceptance checks. Re-run
all graph-codec cases after sharing the parser code. Use the normal capped PR
gates and record edit costs separately from core-query benchmarks.

## Minimal example

This complete program reopens a source document before removing its false fact:

```haskell
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint)
import qualified Data.CFTA.Document as Document
import Data.CFTA.Equality.Constraint (EqConstraints (EqContradiction))
import Data.CFTA.Serialization.JSON (decodeDocument, encodeDocument, explainDecodeError)
import qualified Data.CFTA.Term as Term

main :: IO ()
main = do
    before <- either (fail . Document.explainDocumentError) pure $
        Document.mkDocument ("Atom" :: String)
            [("Atom", [FTA.Transition "zero" [] $ Document.Annotation "zero" $
                Map.singleton "disabled" $ equalityConstraint EqContradiction])]
    reopened <- either (fail . explainDecodeError) pure $ decodeDocument $ encodeDocument before
    let request :: Document.Patch String
        request = Document.patch reopened [Document.RemoveFact "Atom" "zero" "disabled"]
    after <- either (fail . Document.explainDocumentError) pure $ Document.applyPatch request reopened
    let term = Term.Node "zero" []
    print (FTA.accepts (Document.compileGraph reopened) term, FTA.accepts (Document.compileGraph after) term)
```

The result is `(False,True)`. Add `cfta`, `cfta-serialization`, and
`containers` to the caller's dependencies. Keep `before` to undo the edit.
This example needs no solver. See `cfta-editable-document` for the complete
separate-process workflow with equality and semantic facts and a new constructor.

`FTA.terms` lists the underlying ordinary tree shapes without interpreting
constraints. Do not use it to list a compiled document's constrained language.
`FTA.accepts` handles the equality constraints in this minimal example. Use
`Sized.sized` for equality size classes or `Sized.sizedUpTo` with an entailment
solver for semantic guards. The complete executable uses the latter route.

## Validation

The fresh strict build, all six suites, formatting, lint, and metadata checks
pass. The save/edit/show executable runs in separate processes and produces
exactly three equal pairs after the edit.

A standalone probe checks false-fact removal, individual equality removal,
constructor addition and removal, name-based selection after insertion, atomic
forward references and arity changes, missing targets, duplicate names, stale
patches, failed-batch rollback, and unchanged old documents. Its finite fixture
counts are `[0,2,4,8,27,8,3]`. Cyclic size counts and rank inverses replay after
saving and reopening the restored document.

Every existing graph-codec fixture imports as one fact per production, passes
through a document round trip, and compiles back to the exact graph. This
includes every raw formula and guard form. Thirteen malformed document cases
pass. The previous 31 graph errors and all graph rank-replay checks still pass.
Graph version 1 fixture bytes are unchanged. The minimal example compiles and
prints `(False,True)`.

Template exclusion can copy one source annotation to several generated
transitions. The probe confirms that those copies need distinct identities or
retained source provenance before they can become an editable document. Keep
the original source when applying such transformations to a compiled graph.
A reversible filter layer is separate work.
