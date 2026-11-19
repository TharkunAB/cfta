# Causal compatibility progress checkpoint

This archive records bounded diagnostics and two private Lean components after
Source80. It adds no normal-source theorem. Read PROGRESS.md for the strongest
published claim and the open proof obligations. RESULTS.json binds the actual
compiler results, failures, source maps, diagnostic and cleanup results.

Run `python3 verify.py` from this directory. The verifier checks the archive
hashes and the recorded result boundaries. It does not rerun GHC, Lean, or the
diagnostic. The archive contains sources, scripts, exact commands, full logs,
input maps, failed attempts, and the minimal repairs. It contains no compiler
objects, executable binaries, library caches, or copied ancestor archives.

Use `tar -tzf inputs.tar.gz` to list the files. Extract the archive in a separate
checkout or an empty directory. Member paths are relative to the repository
root. The source-first diagnostic commands are in
lean/restart-evidence/20261119-source-fresh-instantiation-occurs-probe-draft/COMMANDS.md.
That file is the historical pre-execution plan; PROGRESS.md and the actual logs
record the completed runs. Rebuild the diagnostic from its three Haskell files.
Check the current Cabal plan before reusing its recorded package IDs.

The original checked source is commit6817cf4bdc2279d764cdc3f52f3a7c353b104b23.
The two successful private components each have one exact standard-axiom report.
The failed ordinary-union attempt has zero proof credit. The later constructor
and stored-encoder drafts are included as OPEN sources with zero proof credit
at this cut. Source80 remains the normal published theorem. This archive does
not prove one model for all historical constraints or original-root acceptance.
