# Exact identity worker metadata erasure

Status: UNCOMPILED. Root must compile both new statements. Created 2026-11-14 at 07:39 CET.

The candidate contains complete proof drafts for the two approved headers: `resume_identity_metadata_erasure` and `runEager_identity_metadata_erasure`. Both headers match the retained plan byte for byte. Both sides erase arbitrary supplied metadata. The same graph, caller, query memos, cache, work fuel, recursive fuel, empty template list, check flag, and edge selector reach both actual workers. Stop is `none`. Order always returns `none`. The supplied narrowing operation is identity.

## Proof structure

The recursive proof uses induction on the actual outer recursive fuel. It generalizes both metadata records, all current native inputs, and the exact `Option Next`. Zero fuel and terminal decisions reduce by reflexivity.

For a positive expansion, the public prefix theorem supplies equality of the two erased actual prefix observations. The proof then splits the two existing prefix values. It retains every metadata-free field. It splits optional raw results into empty, singleton, and multiple rows. It retains each error constructor, Boolean, `Next`, Core, caller, query state, cache, and ordinary observation. A supported parked singleton uses the induction hypothesis at the same returned native inputs. Unsupported observations use the same erased selected failure.

The accepted Right branch invokes a local equality about the actual existing eager preparation. Local names abbreviate the actual `continueWith` calls and actual preparation results. They define no new operational hook or worker. `continue_empty_exact` exposes the same framed cache and restart decision. The lower-fuel induction hypothesis compares the two actual callbacks at arbitrary returned metadata. The checked `prepared_erasure` theorem transports each actual preparation. Equality of the mapped hook functions gives equality of the full native preparation and mapped optional folds. Missing folds retain the actual preparation failure and endpoint. Present folds use the checked `finish_erasure` theorem.

The final theorem unfolds only the actual entry wrappers and the metadata-independent restart decision. It applies the recursive statement at that same decision.

## Scope

The result is exact equality of the existing erased bounded result. It includes complete, stopped, shared, failed, and unsupported observations. List mapping retains order and multiplicity. The statements do not assume completion, adequacy, a model, a selection contract, or a supplied provider. They do not state a Haskell execution theorem. No Haskell files or findings changed.

## Source checks

The source imports the privately checked CPS module. Root check5 contains eight standard-axiom reports and an exit code of zero. The pure maps are pinned to Root map check3. The prefix, actual recursive worker, callback, and restart sources are pinned in `checks.json`. The packet includes no build artifacts.

Both approved headers match exactly. No definition, datatype, map, operational worker, hook, provider, axiom, `sorry`, or `admit` was added. GNU patch adds the exact source with zero fuzz and removes it on reverse replay. All previous packets remain unchanged. These integrity checks do not provide Lean proof credit for the new source. No compiler, Git, live source, Haskell, or board operation ran.
