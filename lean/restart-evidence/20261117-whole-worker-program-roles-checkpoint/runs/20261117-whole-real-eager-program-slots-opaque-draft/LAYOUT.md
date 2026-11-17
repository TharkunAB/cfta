# Opaque ProgramSlots component

Status: FROZEN UNCOMPILED. Root owns all compilation and Source changes.

1. Add the ordinary import in `IMPORTS.lean.txt` before the unchanged owner.
2. Append the shared depth definition from the outer assembly packet.
3. Append this packet's `APPEND.lean.txt` once.
4. Append the captured component and the outer assembly.
5. Append this packet's `PROBES.lean.txt` once for its four declarations.

The exact main header is df6c2330. Its one-line probe is retained separately
in `OPAQUE-PROBE.lean.txt`. The helper headers were frozen before their proofs.
The public02a2 and depth583b declarations are not copied or changed here.
The private helpers use arbitrary `literal`; the earlier SharedDriver helper
signatures fix the source literal. Their small proof algebra is retained.
The owner keeps its inherited 200000 checking setting. No cap is increased.

The old resource spine derives the actual finished Packet, Fits, Heap, mass,
and smaller-depth reservation from the original inputs. That theorem may use
larger-bound replay internally. The role proof does not use its larger-bound
child or finalizer observations. It inverts `completed` to the literal child
and finalizer receipts at the original supplied `workFuel`.

The public observed child law derives ProgramSlots at that literal child
endpoint. The finalizer proof then inverts the actual Finalize.run and
NativeIndex.write equations. It applies the existing unmarked setValue law
at the same write. It does not choose an adequate-fuel finalizer endpoint.
The actual false recording receipt supplies the callback Frame and Packet.
The smaller outer depth hypothesis applies to the exact original tail.

No compiler, Haskell execution, Git, Source edit, Audit edit, board call,
or temporary-directory action was performed for this packet.
