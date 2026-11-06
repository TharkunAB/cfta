# Shared recursion-key getter

Both worker sites call the private `Data.CFTA.Enumeration.recursionKey` helper.
The direct `nodeIdentity` application is inside that helper.
The Source receipt identifies its complete 14-byte application.
It also corrects the manual columns for the call at row 1006.
These Source facts do not resolve the compiler Name or the getter type.

## Actual results

`stage_nominal_probe.py` is the exact executed producer.
It staged two private files from the owned 71748-byte capture.
One file annotates the direct getter application with a candidate qualified `Int`.
The other file uses the unit type `()`.
The producer adds the same qualified `GHC.Types` import to both files.
The import provider and package availability remain unknown.

The producer checked the source fingerprint before the edit.
It checked that reverse edits recover every original byte.
It checked that both worker call slices remain equal after their offsets move.
`staged-probe-metadata.json` contains the resulting hashes and edit maps.
No compiler ran. Neither annotation is accepted evidence of a getter type.
The author manifest predates the actual staging run.
`verification.json` records the executed stages.

The pinned plan selects the local `cfta` library and unit
`cfta-0.1.0.0-inplace`, with configured GHC 9.14.1 labels.
Its `build-info` field supplies an exact path.
That file was absent at three separate checks.
`build-info-availability.json` records this result.
`inspect_declared_build_info.py` is the exact executed metadata inspector.
The plan labels do not establish a compiler ABI or an effective command.

## Reproduction and next step

Start from source with the SHA-256 in `shared-getter-spans.json`.
Check that fingerprint before using any byte offset.
The executed producer has fixed historical paths and physical identities.
For a fresh run, use a new private output prefix and record fresh input pins.
Keep the edit algorithm and its reverse checks.
Do not claim that fresh physical identities match the historical ones.
The private source files and copied build trees are not required artifacts.
The source and the small producer are sufficient to regenerate the variants.

First obtain the effective compiler context for the selected CFTA component.
The existing plan supplies no compiler-argument list.
The declared build-info file cannot supply one while it is absent.
A possible next route is the Cabal library API for existing configuration.
Discover that API with Hypha and verify the installed Cabal version first.
No such API call was made in this checkpoint.
Keep the protected plan and configuration files unchanged.
Use the serial capped runner. Do not copy a build tree.

Then run the candidate and negative variants with the same verified context.
Require the candidate to pass and the unit variant to fail at the annotation.
Disable deferred type errors, deferred typed holes, and deferred scope errors.
Check the actual provider of the qualified primitive import.
Keep diagnostics private until their Source/TYPE scope is admitted.
A successful annotation check would establish a local type fact.
Source-to-loaded-file correspondence, primitive width, ABI, interning laws,
and worker refinement would still require separate proofs.

Cabal documents build metadata with component compiler arguments.
It writes that metadata during a build; this checkpoint started no build.
See the [Cabal build-info option](https://cabal.readthedocs.io/en/latest/cabal-commands.html#cmdoption-enable-build-info).
A custom `-F` preprocessor runs after CPP.
The raw byte offsets must not be applied to that processed input.
See the [GHC 9.14.1 preprocessor options](https://downloads.haskell.org/ghc/9.14.1/docs/users_guide/phases.html#options-affecting-a-haskell-pre-processor).

## Formalization boundary

The strongest checked local theorem remains
`MicroCFTA.SourcePruningEnumerationActionTotal.prepare_total`.
Successful prepared operations preserve `UF.Total` for arbitrary local fuels.
The theorem does not derive worker termination or a common original-input bound.
The two `EnumerationState` workers use abstract Graph and Oracle slots.
Their optimized Haskell realization is not established.
The next primary contract is the actual `nodeEdges` node-handle/view contract
and its relation to `unfoldOuterRec`, followed by native intersection.
No retained dependency makes the held BinderInfo probe a primary requirement.
