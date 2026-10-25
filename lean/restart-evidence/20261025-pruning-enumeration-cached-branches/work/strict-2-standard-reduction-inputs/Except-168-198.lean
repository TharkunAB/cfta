namespace ExceptT

variable {ε : Type u} {m : Type u → Type v} [Monad m]

/--
Returns the value `a` without throwing exceptions or having any other effect.
-/
@[always_inline, inline]
protected def pure {α : Type u} (a : α) : ExceptT ε m α :=
  ExceptT.mk <| pure (Except.ok a)

/--
Handles exceptions thrown by an action that can have no effects _other_ than throwing exceptions.
-/
@[always_inline, inline]
protected def bindCont {α β : Type u} (f : α → ExceptT ε m β) : Except ε α → m (Except ε β)
  | Except.ok a    => f a
  | Except.error e => pure (Except.error e)

/--
Sequences two actions that may throw exceptions. Typically used via `do`-notation or the `>>=`
operator.
-/
@[always_inline, inline]
protected def bind {α β : Type u} (ma : ExceptT ε m α) (f : α → ExceptT ε m β) : ExceptT ε m β :=
  ExceptT.mk <| ma >>= ExceptT.bindCont f

/--
Transforms a successful computation's value using `f`. Typically used via the `<$>` operator.
-/
@[always_inline, inline]
