This is a source-only plan for one finite-round numeric forecast module.
Keep the checked C envelope and every existing proof unchanged.
Use three public heads: stage, fuelBounds and stage_bounds.
Each stage has one exact seed s_i and M_i = s_i.profile.mass.
Enumerate every pair (count,mass) in [0,M_i] × [0,M_i], including both endpoints.
For each pair, compute C at s_i, then the old node schedule at that C.W and SAME s_i.
Join C.output.profile with the old schedule profile for that case.
Concatenate both case alphabets. Do not keep only the C alphabet.
Join all case profiles with s_i.profile and append all case alphabets to s_i.alphabet.
This defines s_(i+1). Iterate N stages before choosing roomBits(s_N.profile).
No case is recomputed at s_N or at another stage's seed.
fuelBounds takes maxima of C.W and nodeNeed(C.W,budget,s_i) over the finite stage/grid image.
The same budget is fixed for all stages and grid cases.
InitialFuel.phaseNeed at a node is definitionally nodeNeed and ignores request and caller.
Thus the second maximum can supply the same bound to each of the nine lower fuels.
Do not use C.L or claim a new lower-fuel correspondence theorem.
Prove stage profile and alphabet retention from cover_ge and append membership.
Compose that retention from i through N, including i = N and N = 0.
For a chosen grid pair, use range membership, finite image membership and cover_member.
Transport the chosen case to s_N with Le.trans and alphabet inclusion.
Apply room_computed once at s_N.profile, then Room.mono for the chosen case.
Use maximum_member for the exact SAME-stage work and lower-fuel entries.
No monotonicity of C, the old schedule, or nodeNeed across seeds is assumed.
No public helper predicate, caller parameter, future Room or success callback is needed.
The theorem does not give Room for the schedule at the common outer maximum.
A later consumer can use the existing stable-success conclusion after success at each case C.W.
The full next warm packet and actual repeated-pass execution remain separate obligations.
The planned count lemma must establish the actual request count and mass are within M_i.
The forecast does not widen a populated caller. Choose one mathematical width before construction.
The forecast gives no practical fixed-width bound or Haskell arithmetic/refinement claim.
Target 210–280 total source lines; hard stop 300 before more implementation or any compiler.
Private membership, retention and finite-image lemmas are sufficient. Do not add another recurrence framework.
All declarations and equations in this package are proposals, not implemented or elaborated code.
The author also authored the C envelope and the ActualParentNativeStores/OuterPrefixNativeStores foundations.
No Lean, Lake, runtime, recurrence evaluation or official source command is authorized for this plan.
