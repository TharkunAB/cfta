# Proof-only let layout repair

UNCOMPILED. Preserve original187 and terminal37245 strict failure log.
Both full component headers, full real-worker target, genuine smaller-depth IH
and probes are byte-exact. The only raw change adds parentheses around the
proof-local change expression and complete continuation-call initializer,
plus an explicit let/body semicolon. This prevents Lean's offside parser from
treating recur graph as the let body. There is no statement, premise, runtime
fuel, source operation, result, cache or outcome change.
