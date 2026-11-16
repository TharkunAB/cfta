# Explicit quantified slot and fragment types

Status: UNCOMPILED. Original82c module failed Root77260 with definition dotted-identifier errors and recovery cascades. It has no proof credit.

This repair changes ONLY the definition's quantified binders: both slot/fragment pairs now explicitly have Nat/Fragment Symbol types; the old/oldFragment pair has the same explicit types. This resolves the actual getElem/constructor expected-type ambiguity. The logical conjunction, clause order, stored-fragment equalities, protected classes and universal old-class avoidance are unchanged. ExpandedBirthHistory's name and before/after signature are unchanged.

ALL FOUR public theorem headers, ALL FOUR proof bodies, preamble and independent probes are byte-exact. No extra premise, model, ordering, separation, runtime operation, cap change or linter disable is introduced. Original936 definition/82c raw/log remain immutable. No Source/compiler/Git/board/tmp action was performed.
