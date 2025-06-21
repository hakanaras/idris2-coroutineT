module Control.Monad.Coroutine.Impl

public export
interface (Semigroup s, Monad m) => Suspension (0 s : Type) (0 m : Type -> Type) where
  resumable : s -> m Bool

mutual
  public export
  data CoroutineImpl : Type -> (Type -> Type) -> Type -> Type where
    MkCoroutine : m (Intermediate s m r) -> CoroutineImpl s m r
  
  public export
  Intermediate : Type -> (Type -> Type) -> Type -> Type
  Intermediate s m r = Either r (Suspended s m r)

  public export
  Suspended : Type -> (Type -> Type) -> Type -> Type
  Suspended s m r = (s, Lazy (CoroutineImpl s m r))

export
runCoroutineImpl : CoroutineImpl s m r -> m (Intermediate s m r)
runCoroutineImpl (MkCoroutine m) = m

pure' : Applicative m => r -> CoroutineImpl s m r
pure' = MkCoroutine . pure . Left

bind' : Monad m => (a -> CoroutineImpl s m b) -> CoroutineImpl s m a -> CoroutineImpl s m b
bind' f (MkCoroutine ma) = MkCoroutine $ do
  a <- ma
  case a of
    Left  a'      => let MkCoroutine fa' = f a' in fa'
    Right (s, mb) => pure $ Right (s, delay $ bind' f mb)

export
Monad m => Functor (CoroutineImpl s m) where
  map f ma = bind' (pure' . f) ma

export
Monad m => Applicative (CoroutineImpl s m) where
  pure      = pure'
  mf <*> ca = bind' (\a => bind' (\f => pure' (f a)) mf) ca

export
covering
Monad m => Monad (CoroutineImpl s m) where
  ma >>= f = bind' f ma