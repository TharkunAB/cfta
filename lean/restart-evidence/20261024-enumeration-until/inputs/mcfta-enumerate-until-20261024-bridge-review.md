# No-stop eager bridge to the existing enumeration driver

Read-only design cut: 2026-10-24 01:01 CEST. No proof body, compiler command, prepared program, repository edit, or new execution was run. Source identities and exact cuts are in `/tmp/mcfta-enumerate-until-20261024-bridge-inputs.json`.

The preferred result is equality of **successful ordered rows**, including the complete final `EnumerationState.State`, with the old unit result changed to `none`. It is stronger than membership equivalence. It does not equate errors or oracle-event traces. The bridge can use existing `ReadOnlyOracle` without `Safe`, `Ready`, `CompleteGraph`, total-forest, intersection, success, or final-state oracle premises.

## Exact interface decision

The additive module/namespace `MicroCFTA.EnumerationUntil` is provisional until Root's declaration gate. Guard's proposed interface is suitable:

```lean
abbrev NodeExpansion (Symbol Guard : Type) :=
  List EnumerationState.Suspended → Nat →
    EnumerationState.EnumerateM Symbol Guard (Fragments.Fragment Symbol)
```

`enumerateOutWith graph expandNode fuel uv` keeps the existing outer worker's reads, ancestry setup, recursive unfolding, ancestry clear, and raw representative-slot write. Only its node expansion callback changes. The shared driver takes arguments in this order:

```text
enumerateUntil graph stop narrow expandAt order oracle fuel oracleState
stop     : Option (OracleState → Nat → Bool)
narrow   : OracleState → Nat → Nat → Nat
expandAt : Nat → NodeExpansion Symbol Guard
```

At positive remaining budget `k`, it uses `enumerateOutWith graph (expandAt k) k uv`. Eager expansion is `expandAt k := EnumerationState.enumerateNode graph k`. A fixed callback closure retained through recursive iterations is not the same finite-fuel policy.

Use the SAME existing modeled `findExpandable`/`pickNext` scheduler. Haskell now selects from cached sets without this model's scanning/path-compression effects. Existing `EnumerationIndexSelection.selection_exact` identifies scheduler results and root information; it does not establish identical full union-find forests. That implementation correspondence remains separate.

## Proposed public theorem headers

These are declaration proposals in the new namespace, with existing `EnumerationState`, `EnumerationCorrectness`, and `EnumerationDriver` opened. They are not assertions of a checked theorem. No old definition is replaced.

```lean
theorem no_stop_eager_successes
    (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle)
    (fuel : Nat) (oracleState : OracleState)
    (before : State Symbol Guard) :
    EnumerationCPSChecked.successes (ExceptT.run
      (enumerateUntil graph none (fun _ _ node => node)
        (fun remaining => enumerateNode graph remaining)
        order oracle fuel oracleState before)) =
      (EnumerationCPSChecked.successes (ExceptT.run
        (enumerateFully graph order oracle fuel oracleState before))).map
          (fun pair => ((none : Option OracleState), pair.2))

theorem no_stop_eager_success_iff
    (graph : Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState)
    (observer : ReadOnlyOracle oracle)
    (fuel : Nat) (oracleState : OracleState)
    (before after : State Symbol Guard) (result : Option OracleState) :
    Success (enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining)
      order oracle fuel oracleState) before result after ↔
      result = none ∧
        Success (enumerateFully graph order oracle fuel oracleState)
          before () after
```

There is no `driverSuccess` or `filterCPS` declaration in the existing Lean sources at this cut. The concrete existing operation is `EnumerationCPSChecked.successes`, a `filterMap` that discards only explicit errors and retains each `(value, fullState)` occurrence. `mem_successes` supplies the membership corollary. If the additive model introduces `driverSuccess`, it should be this transparent projection, not an alias of the desired bridge result.

## Small supporting declarations

The names below are proposed. The statement types use only existing APIs, except for the additive worker itself.

```lean
private theorem successes_bind
    (action : EnumerateM Symbol Guard α)
    (next : α → EnumerateM Symbol Guard β)
    (before : State Symbol Guard) :
    EnumerationCPSChecked.successes
      (ExceptT.run ((action >>= next) before)) =
      (EnumerationCPSChecked.successes (ExceptT.run (action before))).flatMap
        (fun pair => EnumerationCPSChecked.successes
          (ExceptT.run (next pair.1 pair.2)))

private theorem getValue_repeat_value
    (firstFuel secondFuel uv : Nat)
    (before middle after : State Symbol Guard)
    (first second : UVarValue Symbol)
    (firstRead : Success (getValue firstFuel uv) before first middle)
    (secondRead : Success (getValue secondFuel uv) middle second after) :
    second = first

private theorem empty_out_successes
    (graph : Graph Symbol Guard) (firstFuel fuel uv node : Nat)
    (scs : List Suspended) (before readState : State Symbol Guard)
    (empty : graph.node node = .empty)
    (reading : Success (getValue firstFuel uv) before
      (.unenumerated (some node) scs) readState) :
    EnumerationCPSChecked.successes
      (ExceptT.run (enumerateOut graph fuel uv readState)) = []
```

The additive worker should also prove its literal eager specialization:

```lean
theorem enumerateOutWith_eager
    (graph : Graph Symbol Guard) (fuel uv : Nat) :
    enumerateOutWith graph (enumerateNode graph fuel) fuel uv =
      enumerateOut graph fuel uv
```

This worker equation may follow by unfolding the two independently retained worker definitions. The public driver bridge does not follow by definitional equality: its empty-node branch has changed.

`successes_bind` follows from existing `EnumerationCorrectness.run_bind` and finite-list `filterMap`/`flatMap` algebra. It preserves order and multiplicity. It adds no oracle assumption.

For `getValue_repeat_value`, decompose both observations with existing `getValue_success`. Let their lookup results be `firstFound secondFound : UnionFind.Result`. The exact intermediate state is `{before with representatives := firstFound.forest}`. First `findRoot_correct` gives an actual path from `uv` to `firstFound.representative`, and preserves it into that forest. Second `findRoot_correct` gives a path from the SAME `uv` to `secondFound.representative`. `UnionFind.reaches_unique` identifies the roots. Both reads leave `values` unchanged. The two stored `Option.some` equations then identify the values. No property of unrelated forest entries is needed.

For `empty_out_successes`, invert a hypothetical successful outer expansion. Its initial successful read must return the just-observed empty node by `getValue_repeat_value`. Its later `enumerateNode` cannot succeed: fuel zero produces an explicit error; positive fuel rejects `.empty`. `Success`, `success_bind`, `success_failure`, and `reject_unsuccessful` cover both cases. This proof does not infer a new successful representative lookup or assume one terminates.

## Complete induction and branch plan

The single driver induction is on `fuel`, generalized over `oracleState` and `before`. Its complete induction hypothesis is:

```lean
ih : ∀ (oracleState : OracleState) (before : State Symbol Guard),
  EnumerationCPSChecked.successes (ExceptT.run
    (enumerateUntil graph none (fun _ _ node => node)
      (fun remaining => enumerateNode graph remaining)
      order oracle fuel oracleState before)) =
    (EnumerationCPSChecked.successes (ExceptT.run
      (enumerateFully graph order oracle fuel oracleState before))).map
        (fun pair => ((none : Option OracleState), pair.2))
```

`graph`, `order`, `oracle`, and `observer` remain fixed. Apply `ih` only to the actual recursive continuation state and actual threaded oracle state, at the predecessor fuel. No independent completion or cross-fuel uniqueness is used.

- Zero: both drivers have no successful rows.
- Positive fuel: use the same scheduler action and successful intermediate `scanned : State Symbol Guard`; split the same `Next` result. Completion changes only `()` to `none`. Stuck work rejects in both.
- Expansion: retain the same actual `uv`, successful `getValue`, and `UVarValue` cases. Eliminated, enumerated, and absent-node slots reject in both.
- Retain the SAME `checkRepeated` action, result, and full intermediate state. Its true branch clears the same suspended constraints and uses `ih oracleState checked`. Do not assume away recursive graphs or ancestry.
- False repetition, nonempty node: identity narrowing writes nothing. Both pre-oracle actions are identical. The eager worker equation equates the actual expansion actions. Both post-oracle actions are identical. Apply `ih` to each actual successful continuation after its `require` guard.
- False repetition, empty node: new driver rejects before the pre-oracle. Old driver may invoke and fail inside that oracle. For each successful old oracle branch, `observer` gives the exact state equality; successful `require` also leaves it unchanged. `empty_out_successes` then removes every potential successful continuation. Errors need not agree.

The relevant local observation types are fixed: `available : Option (List Nat)`, `selected : Next`, `uv node root : Nat`, `scs : List Suspended`, `fragment : Fragment Symbol`, `repeated beforeReject afterReject : Bool`, `beforeState afterState : OracleState`, and all `scanned/readState/checked/observed/accepted/expanded` binders have the full `State Symbol Guard` type. Their proof binders are literal `Success` facts for the actions above. `observedSame : observed = checked` comes from `observer`, not from a supplied final-state certificate. For the read helper, the only new path facts have exact type `UnionFind.Reaches forest uv root size`; each path is derived from an observed successful lookup. No new typed predicate, structural IH, or generalized validity packet is needed.

## Premises and limits

`ReadOnlyOracle` constrains each successful callback branch's machine state. It still permits rejection, nondeterministic caller-state results, and errors. No total/effect-free native callback premise is added. It is needed here: an arbitrary model oracle can change a selected empty slot to a nonempty slot before old `enumerateOut` rereads it. The old driver can then succeed, while the new driver rejects before that callback. `Safe` on the initial state alone would not prevent this mutation.

Full `Except` equality is false even for a read-only oracle: `failure .invalidSlot` is vacuously read-only. On an empty selected node, the old driver invokes it and produces an error, while the new driver rejects before invoking it. Do not assert error-free execution or event-trace equality as a substitute.

The first theorem is at the SAME finite bound. In an old positive iteration of budget `k`, `enumerateOut graph k` uses representative/read bounds `k+1`, node expansion at `k`, and the outer continuation budget `k-1`. The additive indexed eager policy must retain these exact choices. Existential-fuel equivalence is then a corollary. Existing `representative_moreFuel`, `getValue_moreFuel`, `enumerateOut_moreFuel`, and `enumerateFully_moreFuel` retain exact successful states at larger bounds; they do not justify a mismatched policy by themselves.

This is not a theorem about public `termsPruneUntil`, which always uses shallow expansion. A read-only oracle can reject a fully expanded eager fragment `f[a]` but accept shallow events `f[hole]` and `a[]`. Shallow expansion also changes allocation and callback timing. Observation compatibility and any relationship between final states need a separate theorem.

## Size and review recommendation

For a separate bridge module, estimate 150–190 ordinary lines, with a proposed hard cap of 220: context and public headers 30–40; successful-bind algebra 10–15; read-value identity 15–25; empty-out proof 20–30; driver induction 55–75; membership corollary 8–12. The eager worker equation can stay with the additive worker module. No padding or generalized framework is needed. These are source estimates, not checked line counts. Root must review exact fragments and the literal new driver before a body is authorized.

All source correspondence here is conditional on the additive driver implementing the stated source branches and fuel policy. It does not replace the old definitions, assume the desired equivalence as an input, identify a different scheduler's full forest, or extend the separate original-row/counter proofs.
