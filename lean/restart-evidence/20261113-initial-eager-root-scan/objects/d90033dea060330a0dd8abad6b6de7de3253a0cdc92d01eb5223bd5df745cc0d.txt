# Source Type cone: a concrete hypothesis and its closure seams

Status: bounded read-only HEADER/PLAN. No cone, productivity or occurs theorem is claimed.
No new admission gate, SAT solver, counterexample, probe or source edit is introduced.

1. The source supplies one universe EXPRESSION, not yet one proved native owner.
   CurrentContext.context:52 binds types=allTypes top(current constructorCatalog lib query)
   once and uses it for every component/argument-only generalization and application.
   CurrentContext.typeNode:34 builds rigid encoded query types without binders.
   TypeSyntax.allTypesBody:93 has arrow(var0,var0), four fixed variable leaves and the
   escaped constructor catalog; all guards are Top. allTypes:99 has ONE smart binder.
   GeneralizeSyntax.replace:94 inserts that same universe at schematic leaves and
   otherwise builds finite ordinary constructors. finish:104 changes ordinary root guards.
   Thus ordinary guards need NOT be Top. Generalized repeated-variable classes survive.
   A rigid-only/empty source may never build allTypes. Do not invent a resident U then.
   If U occurs, derive its actual source build site and shared owner from SAME-cache
   two-probe identity/replay, not a standalone allTypes build with unrelated identities.
   BinderProtocol replay and FreshOrdinaryReplay.build_replays:21 are useful primitives.

2. Smallest structural invariant to derive, not to require from the user.
   For actual CLOSED Type operands/live Type cells, stop recursion at that resident U.
   Permit Empty; finite ordinary nodes with arbitrary row lists whose children obey
   the same property; and finite normalized unions of such members. No other Mu occurs.
   Rigid labels outside the universe are allowed ordinary leaves; cone is not TypeIn.
   Ordinary SINGLETON rows are only an initial shape. Unfold(U), required-prefix reads
   and row joins produce MULTI-row ordinary nodes, so singleton-only is not closed.
   Source native Type-field occurrences must be derived through existing source/native
   field observers. Guard-only NativeTypeTrace.Origin does not express this structure.
   This property is not asserted for whole Program roots or all physical heap records.

3. Temporary references and unions matter.
   U's stored body is open over its owner reference. Depth and ordinary probes also
   have their exact protocol references. They are physical support, not live closed Types.
   An auxiliary OPEN proof must track those permitted names and their actual environment.
   Do not silently treat every reference as U or allow an arbitrary intersection name.
   requireAll/editAll expose Mu/union via nodeEdges, then rebuild ordinary nodes along
   finite paths (Equality/Operations.hs:295-302 and331-336). Unfold substitutes U for
   its own body reference (Interned/Operations.hs:145-151). Closed operands should return.
   createUnion:592-606 removes Empty, flattens/deduplicates, collapses a singleton and
   combines an all-ordinary list into Node. Therefore a remaining CLOSED canonical union
   in this cone must contain U. This conclusion needs the actual makeUnion invariant;
   an arbitrary raw union of semantically empty ordinary values would not justify it.

4. Why this would solve the opaque BASE case, conditionally on its proof.
   A Mu in the derived cone is U. A surviving canonical union contains U. Both have a
   concrete finite variable-leaf inhabitant from the existing allTypes witness.
   FiniteTypeWitnesses.TypeIn.member:35 and TypeUniverseMembership.variable_member
   provide source membership; SAME-build closed_language transports it to native meaning.
   No native handle existence or Boolean false is used as a witness.
   This would explain false reachesConstrainedMu when all reachable Mu bodies stay Top,
   but that global preservation/flag statement is UNPROVED, including preprocessing.

5. The decisive pure intersection seam is NO NEW pair binder.
   Interned/Operations.hs:487-505 handles Empty/reset, CLOSED same-node identity and
   repeated pairs before Mu/union/reference cases. Mu cases:506-508 use maybeMu.
   Reference cases:512-513 resolve through the real environment. Ordinary rows:515
   hash-join and intersect corresponding children; guards conjoin.
   maybeMu:543-547 constructs a NEW Mu iff its pair reference survives free in the body.
   Lean Kernel.onNode:123-150 mirrors these branches; MaybeMu.maybeMu:32 checks the
   exact Reference.intersection key. unused:81 is the intended no-binder exit.
   Closed U meet U is a self shortcut. U meet a finite non-U pattern must instead
   unfold U, select/join rows and recurse on smaller pattern children; no repeated
   U/non-U pair may return. Open refs resolve to that SAME U. Proving this is the
   central closure fact. Reusing the self shortcut alone leaves it entirely open.
   A bounded proof can induct on the non-U finite pattern, with an explicit universe
   body/unfold phase and union-member descent. Existing MergedOrdinaryHeight stops at
   unions, so it alone cannot rank this broader closed-cone intersection argument.
   Keep exact native thunk requests/cache hits and replay. Semantic memo correctness
   alone cannot give a structural result tag. Any extra memo preservation fact must be
   derived through actual publication/replay, never supplied as a public cone oracle.

6. Remaining operation closure is real work, not a free corollary.
   reducePartially' returns Mu/union unchanged (Equality/Operations.hs:84-87); ordinary
   require/edit/intersection calls still need the above closure and inherited contexts.
   NativeView.narrowAt:33 reads rows/filters/makeNode; unchanged filtering alone is not
   a physical identity law. Open reads/probe construction must retain their own scope.
   withoutRedundantEdges rebuilds Mu when body alternatives disappear (Interned/Operations
   :755-769). refoldEdges:211-229 repeatedly rebuilds/recognizes unfoldings. Prove these
   retain U's identity/shape, or explicitly derive an equivalent productive universe
   family if identity is too strong. Do not assume either. Source raw and default
   preprocessing are separate domains even if observed examples have the same flag.

7. Exact next bounded cut and what it would NOT finish.
   The header sketch isolates initial same-source cone derivation plus the private
   actual-Type-meet no-pair-reference preservation lemma. No old public header changes.
   If that cut succeeds, lift it through SAME field reads/terminal merges/own allocation,
   retaining full contexts/Memos and the actual supported Type occurrences, not all slots.
   Then use the finite opaque witnesses and actual stored Fragment stratification for
   current-state assignment construction. Stratified:18 controls stored fragment cycles;
   it does NOT by itself reject hidden finite-Type occurs equations.
   Actual terminal/class/path correspondence must connect any source occurs obstruction
   to that fragment dependency/rejection. Dropped nonterminal opaque path requirements,
   source residuals and parked partial-compatible recompletion remain explicit.
   Hence cone/productivity is a promising base-case lemma, not yet the joint original
   root/actual-partial finite witness or a proof of all-input/default completeness.
