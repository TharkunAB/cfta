# Pure initial outer lower-fuel ceilings

Date: 2026-10-18 07:34 CEST.

SourceCurrentOuterInitialFuel.lean has SHA256
`c247db14852765ff82d939de6ba6dfa3d00e6722dd33e4cc5383e1a9de199bf8`.

## Contract

parentNeed uses ParentUniformEnvelope.fuel at the initial guard alphabet and
physical profile. Six mutual functions follow the exact six-phase physical
schedule. nodeNeed is bodyNeed. A zero body reserves zero lower fuel; a
successor body reserves its smaller row pass. Descendants reserve children,
and children reserve the indexed walk. Raw reconstruction and inherited
operations do not consume these nine lower worker fuels.

A nonzero row ceiling is the maximum of three exact demands: Parent at the
entry seed, descendants at the predicted Parent output, and row suffix at
the predicted descendant output. A nonzero walk ceiling is the maximum of
its node at the entry seed and its suffix at the predicted node output.
phaseNeed selects these same functions from the existing literal Phase tag.
It retains the Phase's actual remaining outer fuel.

Five component inequalities let a caller send one common ceiling to each
exact following phase. rows_split and walk_split give both directions of
the corresponding shared-ceiling tests. The definitions themselves retain
all exact phase equations. None of these results uses monotonicity of
Parent fuel in its alphabet or profile. They supply no future state,
completion, graph, resource callback or semantic-result premise.

A uniform bound on each of the nine lower fuel variables can therefore be
split separately at rows and walk. This is distinct from physical Room.
Actual Parent admission still needs initial semantic and resource facts.
To carry the ceiling along a reached execution, a consumer must retain the
exact stage seed changes. Required's separate StepSeed/SeedTrace producer
is intended for that purpose. Mere envelope domination is not a fuel
monotonicity theorem. This module does not assume or prove such monotonicity.

## Checked pure example

outer-fuel-kernels-1 defines a concrete initial alphabet with the empty guard
and a positive [[0],[1]] guard, and a finite physical profile. Its one theorem
uses rowsNeed at outer fuel four as one common ceiling. It bounds the initial
Parent, a genuinely nested Parent at the predicted first Parent output,
and a later row Parent at the predicted descendant output.

The proof composes the exported component inequalities. It does not evaluate
large forecasts or substitute a different smaller alphabet. This is a pure
schedule example. It is not an actual worker execution, a source-language
inhabitance result or an additional termination example.

## Validation

Production strict outer-fuel-direct-3 has a raw log of zero bytes and is
byte-identical to the live module. Canonical outer-fuel-canonical-1 terminates
successfully. Existing dependency warnings are separate from the new strict
source. outer-fuel-public-1 prints all fifteen handwritten declarations:
eight definitions and seven arithmetic theorems. Every declaration has
#check @, full #print and #print axioms with all eight required options.
The selected output has no omission, diagnostic, sorry or printer failure.
Only propext, Classical.choice and Quot.sound are allowed.

The pure example strict log is also zero bytes. Its complete one-pair print
is outer-fuel-kernels-public-1. This component has fifteen public pairs and
one pure constructed pair, and zero actual-worker constructed examples.

All selected workers use the five-minute cap and effective memory.max and
memory.high of 4294967296, with memory.swap.max zero. Readbacks and the
component's unique peak log are retained. No resource queue was changed.

Strict attempt one exposed mutual definitions that required their equation
rewrites, and an invalid trans field on Nat.le. Attempt two used conv_rhs and
conv_lhs tactics that are not available in this Lean environment. The final
proof uses core conv syntax and the exact mutual equations. All immutable
failed sources, raw logs, metadata and limits remain in this directory.

## Boundary

These are finite pure lower-fuel forecasts for a supplied bounded outer
schedule. They do not produce an outer successful run, rule out active-owner
collisions, bound fresh recursive requests independently of that supplied
fuel, prove general recursive termination or establish host Int adequacy.
No Haskell source or runtime correspondence result changes here.
