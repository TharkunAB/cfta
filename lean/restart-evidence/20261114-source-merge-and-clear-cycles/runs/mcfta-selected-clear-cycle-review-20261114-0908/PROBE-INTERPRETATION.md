# Proper constructor-cycle probe

Root ran the unchanged supported Haskell source at size2 with distinct variable names: need :: (a -> F a) -> Bool; i :: b -> b; liftF :: c -> F c. This review read the complete paired logs and checked.json. It did not rerun the probe.

| Route | Public list | Separate typed list | need i | need liftF |
|---|---|---|---|---|
| Raw source root | 1 result; exhausted | 1 run; exhausted | absent after exhaustion | present |
| Default reduced/refolded root | 1 result; exhausted | 1 run; exhausted | absent after exhaustion | present |

Each typed control retains its own complete typed term and its own empty residual list. Its result type is Bool. The need and liftF annotations both contain the same displayed pattern Mu -> F Mu. Equal displayed Mu leaves are truncation markers; the printed term alone does not recover the alias identities or prove a shared finite instantiation. This control does have the simple external finite instantiation a=c=Bool; that observation is separate from a checked original-root language proof.

Both raw and reduced reachesConstrainedMu are False. The raw/default processes exited0 in0.011/0.013s. The receipt reports106 unchanged source pins, including both probe sources. No timeout occurred. Root removed the temporary binaries and objects after retaining their hashes. This review does not recertify the full106-source closure from three files.

These results settle this supported constructor-cycle case only. They establish no Haskell defect and no universal clearing or finite-completion theorem. The report at /tmp/mcfta-finite-completion-source-review-20261114-0754.md remains unchanged.

Exact log and receipt hashes are in SOURCE-PINS.json. Their provider is /tmp/mcfta-proper-type-cycle-probe-20261114-0805.
