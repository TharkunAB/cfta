UNCOMPILED minimal source typing repair after26717.

The first actual diagnostics are at line23. Suspended's constructor fields are
trie,var, while the draft wrote var,trie. Replace ONLY that constructor order:
[⟨.branch[(0,.terminal)],0⟩]. The intended state stays one pending None slot with
a path[0] obligation to itself. No proposition, domain, guard or premise changes.
The d386 header and0290 probe remain byte-exact, as do every proof block.

The reported Safe/count/Ne.symm errors depend on the ill-typed bucket's sorryAx.
They must be re-evaluated after this primary typing fix. No failed proof credit
is claimed. Original packet/log remain immutable. Root owns strict checking.
