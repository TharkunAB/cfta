# Inline preparation diagnostic

The initial inline assembly emitted a Python SyntaxWarning for an unused string literal in a dead conditional branch.
The selected tool sources contain no such branch. They were parsed statically and were not executed.
The warning is retained as a preparation diagnostic. It is not a Lean job or a prepared-tool result.
