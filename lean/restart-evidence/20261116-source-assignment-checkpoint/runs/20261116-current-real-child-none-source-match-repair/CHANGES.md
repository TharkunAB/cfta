UNCOMPILED exact-public-header repair of the two remaining62974 regions.
The dispatcher proof now takes the actual afterQuery phase as ONE tuple,
following the checked source dispatcher case receipt. Splitting its first
projection independently lost the relation to the captured actual action.
Every real action is still derived as no-op/failure/optional/assimilation.
The terminal raw proof now cases the actual raw list, row, Unit and tail.
This avoids naming generated matcher binders by an incorrect guessed order.
All other original proofs,8eae header,99e9 probe and runtime fuels are exact.
