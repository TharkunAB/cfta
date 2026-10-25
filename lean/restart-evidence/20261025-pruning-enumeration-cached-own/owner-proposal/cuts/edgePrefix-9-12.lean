
local instance prefixMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation
