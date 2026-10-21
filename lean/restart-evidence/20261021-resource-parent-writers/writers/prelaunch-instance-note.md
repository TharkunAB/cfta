# Private instance placement

Root identified a known `linter.omit` problem before the first proof command. The private `request_eq` declaration now precedes the global public instances and has one explicit `DecidableEq (EdgeKey Symbol Guard)` parameter. Its proof body is unchanged. The four public definitions and headers keep their exact text and instance order. The original 250-line source remains immutable. This correction ran zero Lean, Lake, or canonical commands.
