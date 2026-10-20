# Persistent graph row updates and resumed source ancestry

Main is `9769fe3e9`. Merge `7ac4534cb` retains the published checkpoint
`2a90c2318`. The pull exited with status 128 because the histories diverged.
The merge
preserves both. The sole conflict was the changelog. Both entries are retained.
FINDINGS commit `2667957ab` records the incoming Haskell scope before import.

Ten paths change upstream. Three earlier Haskell files change: Data.CFTA,
Typing documentation, and TypingSpec. The cfta implementation adds replaceRows
and factors mkFTA validation into validateFTA. A nonempty edit map applies all
inserts/deletes to the existing persistent row map before validation. It checks
the initial state, closure and a ranked alphabet. Just[] retains an empty row.
An empty batch returns the input. Edits can change accepted terms and ranks.
This is a new public implementation obligation. No Lean refinement is claimed.

Typing.hs adds documentation only. Typed finite order can differ from size
order. upToSize uses the generator's size classes, with a route-specific
symbolic fallback that treats each term as an atom. The exact structural size
route remains Data.CFTA.Sized. The new upstream test is source evidence.
No package build or suite was run here. The focused cached-dependency check
is described below.

CONTEXT defines language chains, abstraction extensions, definitional
extensions, lowering and representation levels. docs/language-levels.md is an
investigation and plan. Document codecs, portable checkpoints, named fact
edits and a meta-language frontend remain proposed interfaces. Do not include
them in the set of implemented APIs merely because the plan specifies them.

Source inspection also found a route-dependent Typing documentation
follow-up. The unconditional Binders size-major statement can include an
acyclic graph, which takes the finite route. A valid external-field rank
candidate is recorded in FINDINGS. Its cached-dependency executable aborted
before rank output; no runtime counterexample is claimed. An external agent
must verify it with a fresh matching toolchain before choosing a correction.

The user resumed the full-library goal. The previous proof remains four
public callback-child declarations and one constructed theorem, with default
Audit3475jobs73974dependencies. No new proof or Lean validation is claimed for
this import. All earlier Lean source and evidence bytes are retained. The next work
remains original source ancestry from an actual callback build and lexical
Context. Captures, retained Mu bodies and warm winners need explicit origins.
General renewal, active-owner exclusion, outer completion, convergence and
concrete Haskell refinement remain open.

The publication permission is resolved. The user directly authorized the
2026-10-19 push, and remote formalize was read back at `2a90c2318`. Older approval
notes describe the earlier rejected attempts. The current resume supersedes
the earlier pause. Keep frozen evidence unchanged. Monitor the actual active
thread for fresh usage; the monitor now includes its original October15 log.
The stop threshold remains one percent. No Haskell repair is added.
