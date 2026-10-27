# Checked bridge status

The original report remains unchanged. NativeNarrow v3 passed Root strict-native-narrow-arity-2 with empty output. PrefixArity v2 passed strict-prefix-arity-1 on its first check with empty output. Both final installed source copies match the exact retained snapshots. All recorded limits are 4 GiB with swap disabled.

Root installed build-narrow-receipt-arity-1 passed 2088 jobs with 646 bytes of complete output. The same job also built the separately owned OrdinaryReceiptArity helper. It does not make that helper part of this owned proof. build-prefix-arity-1 passed 1666 jobs with 555 bytes. Reports, full logs, and the failed NativeNarrow v2 snapshot remain separate in root-evidence.

These helpers add actual native Heap conclusions. They do not change existing producer contracts or runtimes. NativeNarrow covers every finite narrow/prepare outcome under current Facts, Heap, and Available. PrefixArity observes the SAME existing PrefixValid and derives Heap at its actual caller from original Context and realized storage. It adds no semantic, Canonical, future successful call, or desired endpoint input. This owned bundle stays OPEN for the ongoing integration and final public cue. No checks ran here.
