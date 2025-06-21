module Control.Monad.Coroutine.CPS

public export
data CPS : (Type -> Type) -> Type -> Type where
  MkCPS : ({0 c : Type} -> (a -> m c) -> m c) -> CPS m a

export
rep : Monad m => m a -> CPS m a
rep m = MkCPS (m >>=)

export
runCPS : Applicative m => CPS m a -> m a
runCPS (MkCPS f) = f pure

export
Functor (CPS m) where
  map f (MkCPS g) = MkCPS (g . (. f))

export
Monad m => Applicative (CPS m) where
  pure a              = MkCPS ($ a)
  MkCPS f <*> MkCPS a = MkCPS (f pure <*> a pure >>=)

export
Monad m => Monad (CPS m) where
  MkCPS ba >>= ckb = MkCPS (\kc => ba (\ka => let MkCPS bb = ckb ka in bb kc))
