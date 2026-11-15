# Induction interface

CorrectAt fixes graph, checkEmpty, edgesOf, recursiveDepth, workFuel, metadata, uv, formulas, solver and root. Its task parameter contains only the literal source data and actual callback frame. Its scope arguments describe the actual immutable entry and current tuple history.

The case hypothesis has the shape produced by well-founded induction on task.work root.limit:

    forall smaller, smaller.work root.limit < currentNil.work root.limit -> CorrectAt smaller

The proof instantiates it at the actual returned parent tuple. It supplies the newly produced Origin and Current and the retained ancestor ledger. It does not ask the IH to certify an arbitrary callback, output, seed or endpoint.

The resource conclusion uses the task's current caller as the native Post origin. The selected return leaves that caller unchanged. The parent task starts at the literal SelectedEdge.finish cache. The immutable tuple scope changes back to the stored outer scope. These are separate indices.

All three existing equality instances remain in the actual-source context. Width is bits + 2 and typing is Unit. No new class, arithmetic bound or runtime parameter is introduced.

A later master proof must establish CorrectAt for all tasks. This packet proves one selected-ledger constructor case under its genuine strict-smaller-task IH. It does not prove the master statement or replace it with this case.
