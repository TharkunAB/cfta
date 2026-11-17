# Proof-only value case repair

Status: **UNCOMPILED**. The failed original packet and its diagnostic log remain unchanged.

The none-action branch now injects the `Except.ok` equality before it eliminates the different Option constructors. The cached singleton rewrite already closes its goal, so the extra `exact cached` was removed.

The scalar proof now cases the actual incoming value before it rewrites the returned core. The final assembly cases the same incoming value before it supplies the shape and stored-bucket terms. This reduces the concrete matches before Lean must compare matchers that capture different proof parameters. The prepared-action field uses reflexivity because the existing cases step has already specialized that goal to `some action = some action`.

The full public header, all private helper headers and bodies, preamble, and probes are byte-exact. No premise, runtime fuel, cap, or linter setting changed. No compiler was run.

Original raw: c87d8e9cc3f885c6c400a15fb5a85343e9035be88f79df849da134d579690e36.
Original diagnostic: ../20261117-shared-shallow-result-footprint-check/normal-module.txt.
