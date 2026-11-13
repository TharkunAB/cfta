# Initial prefix observer repair 1

Status: frozen uncompiled repair for Root's strict check.
The approved header48/4e9e9b8c and preamble14/c2117e0b are byte-identical.
The original231/3f1c19c2 and first failed check1645 remain unchanged.

The done branch first rewrites the actual native observation in prepared.
It then applies the same done-constructor injection as before.
Before checkEq is named, the proof unfolds the four concrete initial caller
constructors. This reduces the actual checked.native.machine.heap projection
to the same supplied heap in the check, lookup and preparation calls.
No observation, endpoint, operation, premise or conclusion was replaced.
The initialRead and Frame derivation is unchanged.

The patch contains these two proof-only changes. No compiler, live source,
Git, board or Haskell command was run.
Original failure: /tmp/mcfta-initial-prefix-origin-check1-20261113-1645/.
