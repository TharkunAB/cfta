# Same-file strict check

Status: UNCOMPILED. No proof credit.

Start with a byte-exact full copy of SharedEagerReservation source d207bfaf. Prepend DEPENDENCY-IMPORTS.lean.txt at the top of the copy. Append APPEND.lean.txt and then PROBES.lean.txt. The appendable section contains no imports. It uses only ordinary same-file private declarations. It needs no pending rows, task, or scan proof.

The dependency import names the existing public observed-opaque theorem. Root owns dependency builds, compiler checks, Source promotion, and all66 validation. No visibility changes or encoded private names are used.

The original any-budget identity declaration c831 and prepared-scan declaration bab8 remain unchanged. This helper is an input to their actual same-budget composition. It does not prove real-narrow execution, finite joint completion, or Haskell correspondence. No Haskell change or defect was found.
