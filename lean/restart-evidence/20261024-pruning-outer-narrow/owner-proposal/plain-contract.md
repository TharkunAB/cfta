# Public contract

narrow returns the existing actual Result. It exempts Mu before checking incoming raw type membership. It uses the original raw uv and incoming metadata.typing for the fallback key. It changes no metadata.

narrow_mu is an unconditional same-value/same-heap equation for every fuel. narrow_type is the same equation under incoming raw membership for every Value shape. narrow_fallback is an exact equation under non-Mu and non-membership, including actual failures and their final heaps.

narrow_complete derives one completed actual run from initial Ready, Available and closedness. It returns that run's fuel/result/after, Keeps before after, Available after result, result.free=[], and the identical completed result/after at fuel+extra for every extra. The two bypasses return the original heap; the fallback need not. It has no final-state certificate premise, semantic typing law, success oracle or Ordinary conclusion.
