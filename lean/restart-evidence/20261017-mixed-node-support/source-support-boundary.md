# Current source gate and the remaining general support boundary

Source main is c0cc8a05. This note adds no Haskell defect or behavior change.
The relevant source is cfta/src/Data/CFTA/Equality/Operations.hs.

The class partition uses meetsConstrainedMu on the original child forest.
It computes refused classes before requireAll and the tail-first class fold.
Each retained class then captures the forest returned by earlier edits.
Different classes can overlap. The partition does not recheck the changed
forest before every later class.

The source gate does not require every selected endpoint to be hereditary.
nodeMeetsConstrainedMu returns False for a closed value with no nested Mu.
An ordinary endpoint can therefore have a nonplain own guard and still pass
the recursive refusal check. A theorem that requires hereditary annotations
at all retained leaves covers an intermediate family. It does not establish
coverage of every class admitted by the current source.

The finite ordinary full-pass theorem already covers ordinary constrained
endpoints without Mu. The current mixed-table node theorem covers Region
inputs and permits arbitrary other owners. The remaining combination must
cover finite constrained ordinary layers above recursive values and their
actual intersection, editing, inherited descent, and repeated class schedule.

The existing local native annotation store gives a result annotation when
both actual operands and their source bindings have annotations. It does
not give arbitrary positive-cap closure. A supported ordinary body also
does not by itself give support for a new Mu wrapper. The Mu support case
requires hereditary annotation of its body at every remaining path.

One candidate for a later proof follows the actual native pair schedule.
While one operand traverses a finite constrained layer, prove that the
current mixed pair cannot recur. Then prove that optionalBinder skips a
nonhereditary body because it contains no reference to that pair. At a pair
of hereditary Mu operands, use hereditary closure for the retained binder.
This is a proposed scope and pair-occurrence argument. No such theorem or
general termination result is claimed in this checkpoint.

The exact source refusal policy and inherited equality payloads must remain
in the final general theorem. Do not replace them with a smaller initial
family and report whole-library completion. Language inclusion alone does
not prove guard annotations or a decreasing structural measure.
