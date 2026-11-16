UNCOMPILED proof-scope repair. Original93fb and failed6782 remain unchanged.

The original frozen header contains the old local name EnumGuard in the literal
action type. The other core types already use the concrete Constraint guard.
Add one local notation EnumGuard => Constraint. It has no binder, runtime effect,
premise or checking-budget effect. Every complete public header byte c6d541e9,
probe byte, and every actual proof byte remains exact. No variable or implicit
parameter is added. autoImplicit remains false. This resolves the intended real
worker guard; it does not generalize the fixed core or invent a guard provider.

The NoneBuckets dependency48cf now passed30459 and is public Source.
