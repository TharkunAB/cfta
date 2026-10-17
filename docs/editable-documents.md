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

Use `document 2;` in the complete readable serialization format. Source rows
store stable production names and separate named constraints. Duplicate states,
production names and fact names are errors. Exact round trips retain names,
facts, ordering and the complete graph. Graph and document headers remain
distinct. Query plans, cursors and patches are not stored here.

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
import Data.CFTA.Serialization.Text (parseDocument, printDocument, explainTextError)
import qualified Data.CFTA.Term as Term

main :: IO ()
main = do
    before <- either (fail . Document.explainDocumentError) pure $
        Document.mkDocument ("Atom" :: String)
            [("Atom", [FTA.Transition "zero" [] $ Document.Annotation "zero" $
                Map.singleton "disabled" $ equalityConstraint EqContradiction])]
    reopened <- either (fail . explainTextError) pure $ parseDocument $ printDocument before
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

## Initial validation (before the text-format replacement)

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

## Cost

All eight standard benchmark cells retain their checksums against main
`c0cc8a05`. All six executables are byte-identical. Instruction differences
are below 0.11%; allocation differences are below 0.01%.

The existing 10,000-state JSON round-trip probe still produces 1,437,836 bytes.
Sharing the codec takes 6,137,418,220 instructions and 1,719,601,536 allocated
bytes: increases of 0.082% and 0.052% over the graph-only implementation.

A separate probe constructs a 10,000-state chain and changes one named fact
100 times. Each patch checks its starting document and validates the result.
It takes 8,489,876,796 instructions and 1,513,082,288 allocated bytes, with
2,143,752 bytes of sampled maximum residency. Its checksum is 100 applied facts.
These totals include initial construction. No counts, solver results, or query
indexes are reused. Incremental document validation and persistent row-update
integration remain follow-ups.

Measurements use GHC 9.14.1 at `-O2` with the workspace dependency settings.
All local jobs run serially through heavy-management with 12 GiB process caps
and 4 GiB RTS caps.

## Direct named-production edits

Add `PutTransition state transition` and `DeleteTransition state name` to the
same atomic patch API. The target state must exist. `PutTransition` uses the
name in the supplied annotation. It replaces that production in place, or
appends it when the name is new. The complete supplied production replaces the
old one, including its facts. Other productions and their order stay unchanged.
Use `SetFact` when only one fact needs to change.

`DeleteTransition` requires a unique existing name. Removing the last production
leaves an empty state row. Neither operation renumbers the remaining names.
An ambiguous name introduced earlier in the batch is an error. Graph references
and symbol arities are still checked after the complete batch. These edits do
not change the snapshot format: patches are not serialized by that format.

Use `PutTransition` in the source-editing example to add `two` directly. Verify
append and replacement order, removal of the last production, retained facts on
other productions, missing states and names, ambiguous names, stale patches,
atomic forward references, and simultaneous global arity changes. Compare
compiled terms with the equivalent complete-row edits and retain all existing
source-document and graph-codec checks.

The direct operations pass the fresh strict all-component build, all six test
suites, formatting, lint, and metadata checks. A focused probe verifies append,
replacement, deletion, retained order and facts, missing and ambiguous targets,
new productions followed by fact edits, stale patches, final-batch validation,
and equivalence with complete-row edits. The prior document probe also passes.
The saved edited example is byte-identical to the complete-row version.

These operations are the low-level source edit layer. The primary user interface
will compose language expressions for constructor and fact changes and named
term or subtree exclusions. Saving the resulting value is a persistence step.

The direct-edit change retains all eight standard benchmark checksums. The six
core executables are byte-identical to main. Instruction differences are below
0.11%, and allocation differences are below 0.01%. The shared JSON and 100-fact
edit probes remain within 0.01% of the preceding document implementation.

`DefineTransition state name symbol children` changes a constructor while
retaining all facts on an existing named production. A new name appends a
production with no facts. `Data.CFTA.Language.define` uses this operation.
`PutTransition` remains the explicit complete replacement, including its facts.
