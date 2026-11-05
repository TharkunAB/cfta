# Selected-step observed totality draft

This draft is incomplete. It is not a compiler candidate. It has not been
elaborated or checked. The `.lean.txt` suffix excludes it from normal Lean builds.

The statement keeps the fixed target: eight gates, five fuel witnesses, and
nine universal binders. It uses the actual selected-step receiver. The proof
reuses the published checked-total producer and splits the observed outer cases.
It stops at the successful singleton-action case. The remaining proof must
establish totality for that action's returned representatives.

The next unreceived dependency contracts are `Membership.mem` and
`List.instMembership`. An actual environment lookup identifies both as definitions.
Their owners are `Init.Prelude` and `Init.Data.List.Basic`, respectively.
This lookup grants no permission to unfold their values.

No extra premise was added. No theorem, runtime correspondence, or global
completion is claimed. Preserve the earlier partial247 incident and receiving255
STOP. This draft does not contain the private expanded equation from partial247.

The source draft has 5465 bytes. Its SHA256 is
`a878b7a69fe8aab96d5fce5d9eb183596f1de752f6f638067ed1b9208a6a7d4a`.
The original scratch file remains unchanged. The full common-bound proof and
Haskell correspondence remain open. No Haskell source fix was made.
