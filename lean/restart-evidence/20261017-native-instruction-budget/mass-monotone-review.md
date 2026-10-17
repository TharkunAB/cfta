# Monotone recursive mass schedules

Recorded: 2026-10-17 07:28 CEST.

The frozen production source is `SourceCurrentAllocatedRecursiveMassMonotone.lean`, SHA-256 `707fa9615c64ef7cf024d9af0a680e12647fa2b5a7cec5da1ec1581beb1fe57c`. Its absolute-path strict first check exited 0 with an empty log. The single delegated canonical target completed successfully in `mass-monotone-canonical-1.log` with 1206 jobs. That log replays an existing dependency warning. The new module has no warning.

The eight public theorems cover the existing MassTrace schedules. `ceiling_mono` and `charge_mono` increase the initial payload bound. `massAfter_bound_mono` and `credit_bound_mono` retain a fixed instruction count. `massAfter_count_mono` and `credit_count_mono` increase that count. `massAfter_mono` and `credit_mono` combine both inequalities, in count-then-bound argument order. The statements hold for every natural bound, including zero. They have no source, domain, store, execution, or support premise.

The private proof adds the missing width monotonicity of UniformMass.evolve. It reuses the existing fixed-width bound and count monotonicity. The optional-binder ceiling increases its width, exponent-derived growth count, and starting bound. The common ceiling also increases the literal squared Work limit. Count monotonicity of the accumulated schedules reuses their existing add/composition laws. No new resource recurrence or allocation accounting was introduced.

`mass-monotone-public-1.log` checks all eight public declarations with full explicit signatures and axiom reports. `mass-monotone-kernels-2.log` checks two integration declarations. Both checks exited 0 with no warning, error, sorryAx, or output truncation. All reported axioms are standard: propext, Classical.choice, and Quot.sound.

The first kernel transports an arbitrary actual certified checked prefix through WidthTrace.prefix_bound. It enlarges both the initial mass and instruction count, and retains the exact reached Good state, Stored bound, control certificate, node and edge supply bounds, and domain bound. It assumes the actual prefix and its numeric length inequality. It supplies no future width or intermediate heap bound.

The second kernel constructs raw self-Mu syntax from the empty constructor heap. It derives its initial Good state and computed store bound. It constructs a two-step physical cold publication/finish trace, observes the exact returned native cell, and constructs an exact warm repeat. It then enlarges the actual two-step count to four and the initial mass to initialBound+3. It derives the same final store, result mass, and supplies at those larger symbolic budgets. No completed execution, source Facts, intermediate store, or desired output bound is a premise. The large numeric ceilings are not evaluated.

This module transports a proved instruction budget. It does not derive that budget from initial source syntax or semantic rank, prove a new query completion theorem, or count runtime instructions inside an atomic checked Work or optionalBinder. Current word admission, semantic correspondence, and later-query resource production remain separate. No Haskell file was changed and no new Haskell defect was identified.

The first imported kernel attempt and its raw failure are preserved. It failed at an omitted explicit type for its resultPost binder. The second attempt is the final clean integration check. Production passed on its first attempt and was not changed afterward.
