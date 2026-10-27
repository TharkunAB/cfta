{- | Enumeration of constrained automata.

One enumerator serves every constraint theory. It builds 'TermFragment's
before expanding them to concrete @Term@s. The path equalities of a
constraint ('equalities') are suspended obligations that point at UVars:
when enumeration descends through an edge, those obligations descend with
it, and when one reaches the node it names, the UVars are merged so future
choices stay consistent. A constraint with a 'residual' beyond its
equalities is recorded with the subterm it guards, and 'runs' hands those
pairs to the caller to decide. 'terms' lists an automaton with no
constraint and no recursive binder level by level, without the enumeration
state. A cyclic one always uses the enumeration state, and enumeration stops
at a recursive binder. Only 'plainTerms' lists a cyclic graph without
constraints, as an infinite lazy list.

Most callers use 'terms' or 'runs'. The lower-level state operations are
exposed for pruning oracles and downstream tools that need to inspect or
steer enumeration.
