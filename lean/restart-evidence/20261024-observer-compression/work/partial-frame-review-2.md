# Partial-render frame candidate V2 review

Reviewed 2026-10-24T02:19:12+02:00. Status: SOURCE_CLEAR.

Personally read the complete selected87-line source and exact V1→V2 diff. The sole change joins the newline and indentation after `using` to its existing getValue_moreFuel operand. Replacing that one span in retained V1 reconstructs V2 exactly. Every theorem statement and proof token is unchanged. Installed EnumerationPartialObservation.lean is byte-identical to V2.

expandPartial_frame assumes only Total before.representatives and the supplied successful partial render. It concludes the complete Frame: counter, values, obligations, both ancestry fields and every root path with its root ID and size. It does not conclude equal forests. The ordered child traversal composes actual frames; only enumerated payloads recurse after a value read.

expandPartial_moreFuel retains the identical successful partial term AND complete after state on the SAME initial state. It adds no validity/completion premise. It does not compare equal fuel across two different forests or assert unconditional termination.

The concrete boundary is intact: only unenumerated(Some recursive node, []) truncates. Nonempty suspended constraints stay pending holes. Other pending/eliminated cases retain the original queried UVar ID. Missing reads and fuel exhaustion are not converted into fabricated output. No output-agreement/transport theorem or arbitrary oracle congruence is included.

Root's first check failed at Lean layout before this repair; the retained first receipt/log remains. The selected second receipt reports exit0 with an empty log and explicit warnings-as-errors/all-linters. I inspected those records without running a compiler or selected program. I authored V1; Root authored the layout repair and owns compilation. No repository edit, Git mutation, network or board operation was performed.

Checked identities:

| Input | Bytes | SHA256 |
| --- | ---: | --- |
| `/tmp/mcfta-observer-frame-20261024-partial-frame.lean.txt` | 4676 | `dbd3e9b006972cece23378f433b777867c1d50a225df69f6a8ee09420c3d8cc3` |
| `/tmp/mcfta-observer-frame-20261024-partial-frame-2.lean.txt` | 4664 | `a59184eea5e21214ab912d77a5d75d014f60f72aa0d83a6c6dac0ea072e76640` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationPartialObservation.lean` | 4664 | `a59184eea5e21214ab912d77a5d75d014f60f72aa0d83a6c6dac0ea072e76640` |
| `/tmp/mcfta-observer-frame-20261024/partial-frame-install.json` | 272 | `16a639c35c684f1477afa40500e3afe263c27eeca77a3f75ec7d63d10c42193b` |
| `/tmp/mcfta-observer-frame-20261024/partial-frame-check-1/report.json` | 511 | `7e4290778217e6f300cf989d43a28d6aa94178237fcabd6fae506eede5a6bde7` |
| `/tmp/mcfta-observer-frame-20261024/partial-frame-check-1/raw.log` | 1599 | `34908a78d31fef39bcc8d47443712fd819a095124f06af1dd2b9fb2f4b1ab159` |
| `/tmp/mcfta-observer-frame-20261024/partial-frame-check-2/report.json` | 508 | `f08f8d8be1d1065da98af41513345340b3c7205101c6072c20bb638343d02aba` |
| `/tmp/mcfta-observer-frame-20261024/partial-frame-check-2/checked.lean` | 4664 | `a59184eea5e21214ab912d77a5d75d014f60f72aa0d83a6c6dac0ea072e76640` |
| `/tmp/mcfta-observer-frame-20261024/partial-frame-check-2/raw.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
