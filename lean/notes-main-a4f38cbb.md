# Main a4f38cbb source refresh

Main `a4f38cbb` is merged at `a140c37b`.
Only `.github/workflows/ci.yml` changes from `6baa0e25`.

The workflow adds manual workflow_dispatch. Release-artifact validation now
runs for push or manual events. It no longer runs on pull requests.
The existing push trigger remains restricted to main.
No build command, package, Haskell implementation, test, or benchmark changes.

The earlier strict Nix validation at `6baa0e25` remains applicable:
all libraries, executables, tests, and benchmarks build with strict warnings;
all six suites pass, with 755 examples plus golden; Fourmolu passes eight
changed Haskell files; Cabal-gild passes four packages.
These checks were not repeated for the CI-only refresh.

The new proof scope and historical emptiness-body gap are recorded in
[the conjunction completion note](notes-current-conjunction-completion.md).
A green audit of the older Decision/Scan graph does not identify it with
the later conjunction source algorithm. The full-library goal remains active.
