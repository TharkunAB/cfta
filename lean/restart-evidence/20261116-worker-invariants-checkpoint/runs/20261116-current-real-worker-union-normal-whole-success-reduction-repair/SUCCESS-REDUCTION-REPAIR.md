# Actual successful child reduction repair

Frozen: 2026-11-16 07:02 CET. UNCOMPILED. Original389 rawecd8 and Root23763 failure remain immutable.

Before cases on the actual Finalize.run scrutinee, dsimp only now reduces the already concrete successful singleton child tuple. The earlier goal still hid that finalizer under a tuple/list matcher, so cases did not rewrite its hidden occurrence. The reduction preserves the same actual call and endpoint.

The exact two compiler-reported unused simp arguments are removed: ite_false from the positive classifier branch and ite_true from the negative branch. No other proof changes. Complete original dfcf/aa7011fa headers and probes, all public premises, configurations, runtime fuels and every other proof remain exact. No linter, limit or Source change.
