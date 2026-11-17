# Concrete tuple receipt and selected callback repair

Status: UNCOMPILED. The original 95d22 packet and strict94884 source/log are unchanged. All six first component headers, both predicate spellings and all probes remain byte-exact. The c316 wrapper is unchanged and is maintained by Root.

The tuple cons proof now supplies the constructor's actual configuration, literal done/stopped callbacks, middle caller/cache/query, fragment, exit, output indices, path/position and event lists explicitly. This avoids inferring higher-order callback metavariables from a partial constructor application. Three reported unused simp arguments are removed.

The selected-row proof retains currentSnapshot before destructing Current. It uses the already retained entrySnapshot after the previous prefixInputs destruct. Its selected receipt rewrite now applies afterSame before fragmentSame, so the newly introduced residual fragment is rewritten in the same goal. No witness, Packet or source state is replaced.

All other proof bytes remain unchanged. The checking limit remains 200000. Runtime workFuel and recursiveDepth are unchanged. No axiom, sorry, new premise, linter suppression, alternative callback, future supplier or model assumption is added.

Use the same import+exact old owner+checked entry factor+main append+closed c316 wrapper layout as the first packet. The normal guarded ledger helper is already verified. This packet has no proof credit before Root's whole-module check passes.
