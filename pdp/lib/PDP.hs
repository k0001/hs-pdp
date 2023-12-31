{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

module PDP {--}
   ( Proof
   , type (-->)
   , TRUE
   , FALSE
   , AND
   , AND1
   , OR
   , OR1
   , NOT
   , NOT1
   , XOR
   , XNOR
   , axiom
   , PDP.id
   , PDP.const
   , lift
   , mp
   , ($*)
   , mt
   , rmap
   , lmap
   , andSwap
   , and1Swap
   , orSwap
   , or1Swap
   , true
   , or1
   , unOR1
   , and1
   , unAND1
   , dmAND
   , dmAND1
   , dmOR
   , dmOR1
   , PDP.curry
   , PDP.uncurry
   , unOR
   , PDP.or
   , left
   , right
   , mapLeft
   , mapRight
   , PDP.and
   , mapFst
   , mapSnd
   , PDP.fst
   , PDP.snd
   , absurd
   , not1
   , unNOT1
   , Prove2 (..)
   , prove2E
   , prove2S
   , prove2F
   , prove2T
   , Prove1 (..)
   , prove1E
   , prove1S
   , prove1F
   , prove1T
   , Prove (..)
   , Description1 (..)
   , LT
   , lt
   , LE
   , le
   , EQ
   , eq
   , GE
   , ge
   , GT
   , gt
   , NE
   , ne
   , neSym
   , notGE
   , geLE
   , geTrans
   , notLE
   , leGE
   , leTrans
   , notGT
   , gtLT
   , gtNotLE
   , gtAsym
   , gtTrans
   , notEQ
   , eqRefl
   , eqSym
   , eqTrans
   , notLT
   , ltGT
   , ltAsym
   , ltTrans
   , ltNE
   , gtNE
   , Named
   , pattern Named
   , type (@)
   , unsafeNamed
   , unsafeMapNamed
   , unNamed
   , name
   , Refined
   , pattern Refined
   , type (?)
   , unRefined
   , unsafestRefined
   , mapRefined
   , unsafestMapRefined
   , refined
   , refineT
   , refineS
   , refineF
   , unsafeRefine
   , refine1T
   , refine1S
   , refine1F
   , unsafeRefine1
   , mapRefine1T
   , mapRefine1S
   , mapRefine1F
   , unsafeMapRefine1
   , rename
   , forRefined
   , traverseRefined
   ) -- }
where

import Control.Monad
import Control.Monad.Catch (Exception, MonadThrow, throwM)
import Data.Aeson qualified as Ae
import Data.Bifunctor
import Data.Binary qualified as Bin
import Data.Coerce
import Data.Csv qualified as Csv
import Data.Fixed
import Data.Int
import Data.Kind (Type)
import Data.Scientific (Scientific)
import Data.Singletons
import Data.Tagged
import Data.Time.Clock qualified as Time
import Data.Word
import GHC.Show (appPrec1)
import GHC.Stack
import Numeric.Natural

--------------------------------------------------------------------------------

data Proof (p :: k) = QED
   deriving (Show)

type a --> b = NOT a `OR` b
type (-->) :: a -> b -> Type
infixr 0 -->

data TRUE

data FALSE

data AND l r
type AND :: l -> r -> Type
infixl 7 `AND`

data AND1 f g x
type AND1 :: (x -> fx) -> (x -> fx) -> x -> Type
infixl 7 `AND1`

data OR l r
type OR :: l -> r -> Type
infixl 5 `OR`

data OR1 f g x
type OR1 :: (x -> fx) -> (x -> fx) -> x -> Type
infixl 5 `OR1`

data NOT a
type NOT :: a -> Type

data NOT1 f x
type NOT1 :: (x -> fx) -> x -> Type

type XOR l r = (l `AND` NOT r) `OR` (NOT l `AND` r)
type XOR :: l -> r -> Type
infixl 4 `XOR`

type XNOR l r = (l `AND` r) `OR` NOT (l `OR` r)
type XNOR :: l -> r -> Type
infixl 4 `XNOR`

axiom :: Proof a
axiom = QED

id :: Proof (a --> a)
id = axiom

const :: Proof (a --> b --> a)
const = axiom

-- | @
-- 'lift' f '$*' a  ==  f a
-- 'mp' . 'lift' ==  'id'
-- @
lift :: (Proof a -> Proof b) -> Proof (a --> b)
lift !_ = axiom

-- | @
-- 'lift' f '$*' a  ==  f a
-- ('$*') == 'mp'
-- @
($*) :: Proof (a --> b) -> Proof a -> Proof b
($*) = mp

infixl 4 $*

-- | @
-- 'mp' . 'lift' ==  'id'
-- @
mp :: Proof (a --> b) -> Proof a -> Proof b
mp !_ !_ = axiom

rmap :: Proof ((b --> c) --> (a --> b) --> (a --> c))
rmap = axiom

lmap :: Proof ((a --> b) --> (b --> c) --> (a --> c))
lmap = axiom

andSwap :: Proof (AND l r --> AND r l)
andSwap = axiom

and1Swap :: Proof (AND1 f g x --> AND1 g f x)
and1Swap = axiom

orSwap :: Proof (OR l r --> OR r l)
orSwap = axiom

or1Swap :: Proof (OR1 f g x --> OR1 g f x)
or1Swap = axiom

true :: Proof TRUE
true = axiom

or1 :: Proof (OR (f x) (g x) --> OR1 f g x)
or1 = axiom

unOR1 :: Proof (OR1 f g x --> OR (f x) (g x))
unOR1 = axiom

and1 :: Proof (AND (f x) (g x) --> AND1 f g x)
and1 = axiom

unAND1 :: Proof (AND1 f g x --> AND (f x) (g x))
unAND1 = axiom

dmAND :: Proof (OR (NOT l) (NOT r) --> NOT (AND p q))
dmAND = axiom

dmAND1 :: Proof (OR1 (NOT1 f) (NOT1 g) x --> NOT1 (AND1 f g) x)
dmAND1 = axiom

dmOR :: Proof (AND (NOT l) (NOT r) --> NOT (OR p q))
dmOR = axiom

dmOR1 :: Proof (AND1 (NOT1 f) (NOT1 g) x --> NOT1 (OR1 f g) x)
dmOR1 = axiom

-- | Modus Tollens.
mt :: Proof (a --> b) -> Proof (NOT b) -> Proof (NOT a)
mt !_ !_ = axiom

infixl 4 `mt`

curry :: Proof ((AND a b --> c) --> a --> b --> c)
curry = axiom

uncurry :: Proof ((a --> b --> c) --> AND a b --> c)
uncurry = axiom

unOR :: Proof ((OR a b --> c) --> AND (a --> c) (b --> c))
unOR = axiom

or :: Proof ((a --> c) --> (b --> c) --> OR a b --> c)
or = axiom

left :: Proof (a --> OR a b)
left = axiom

right :: Proof (b --> OR a b)
right = axiom

mapLeft :: Proof ((a --> a') --> OR a b --> OR a' b)
mapLeft = axiom

mapRight :: Proof ((b --> b') --> OR a b --> OR a b')
mapRight = axiom

and :: Proof (a --> b --> AND a b)
and = axiom

mapFst :: Proof ((a --> a') --> AND a b --> AND a' b)
mapFst = axiom

mapSnd :: Proof ((b --> b') --> AND a b --> AND a b')
mapSnd = axiom

fst :: Proof (AND a b --> a)
fst = axiom

snd :: Proof (AND a b --> b)
snd = axiom

absurd :: Proof (FALSE --> a)
absurd = axiom

not1 :: Proof (NOT (f x) --> NOT1 f x)
not1 = axiom

unNOT1 :: Proof (NOT1 f x --> NOT (f x))
unNOT1 = axiom

--------------------------------------------------------------------------------

newtype Named (n :: k) (a :: Type) = MkNamed a
   deriving newtype
      ( Eq
      , Ord
      , Show
      , Ae.ToJSON
      , Csv.ToField
      , Csv.ToRecord
      , Csv.DefaultOrdered
      )

type role Named nominal representational
type (@) = Named

unsafeNamed :: forall n a. a -> n @ a
unsafeNamed = coerce
{-# INLINE unsafeNamed #-}

unNamed :: forall n a. n @ a -> a
unNamed = coerce
{-# INLINE unNamed #-}

pattern Named :: forall n a. a -> n @ a
pattern Named a <- (unNamed -> a)
{-# COMPLETE Named #-}

name
   :: forall {kn} a b
    . a
   -> (forall (n :: kn). n @ a -> b)
   -> b
name a f = f (MkNamed a)
{-# INLINE name #-}

unsafeMapNamed
   :: forall {kn} a b (n :: kn)
    . (a -> b)
   -> n @ a
   -> n @ b
unsafeMapNamed f = \(Named a) -> unsafeNamed (f a)
{-# INLINE unsafeMapNamed #-}

--------------------------------------------------------------------------------

data Disproved = Disproved String
   deriving stock (Eq, Show)
   deriving anyclass (Exception)

--------------------------------------------------------------------------------

newtype Refined (p :: kn -> kp) (a :: Type) = MkRefined a
   deriving newtype
      ( Eq
      , Ord
      , Show
      , Ae.ToJSON
      , Csv.ToField
      , Csv.ToRecord
      , Csv.DefaultOrdered
      )

type role Refined nominal representational
type a ? p = Refined p a

unsafestRefined :: forall p a. a -> a ? p
unsafestRefined = coerce
{-# INLINE unsafestRefined #-}

unRefined :: forall p a. a ? p -> a
unRefined = coerce
{-# INLINE unRefined #-}

pattern Refined :: forall p a. a -> a ? p
pattern Refined a <- (unRefined -> a)
{-# COMPLETE Refined #-}

unsafestMapRefined
   :: forall {kn} {kp} (p :: kn -> kp) a b
    . (a -> b)
   -> a ? p
   -> b ? p
unsafestMapRefined f = unsafestRefined . f . PDP.unRefined
{-# INLINE unsafestMapRefined #-}

mapRefine1S
   :: forall {kn} {kp} (p :: kn -> kp) a b
    . (Prove1 p b, Description1 p)
   => (a -> b)
   -> a ? p
   -> Either String (b ? p)
mapRefine1S f = refine1S . f . PDP.unRefined
{-# INLINE mapRefine1S #-}

mapRefine1T
   :: forall {kn} {kp} (p :: kn -> kp) a b m
    . (Prove1 p b, Description1 p, MonadThrow m)
   => (a -> b)
   -> a ? p
   -> m (b ? p)
mapRefine1T f = refine1T . f . PDP.unRefined
{-# INLINE mapRefine1T #-}

mapRefine1F
   :: forall {kn} {kp} (p :: kn -> kp) a b m
    . (Prove1 p b, Description1 p, MonadFail m)
   => (a -> b)
   -> a ? p
   -> m (b ? p)
mapRefine1F f = refine1F . f . PDP.unRefined
{-# INLINE mapRefine1F #-}

unsafeMapRefine1
   :: forall {kn} {kp} (p :: kn -> kp) a b
    . (Prove1 p b, Description1 p)
   => (a -> b)
   -> a ? p
   -> b ? p
unsafeMapRefine1 f = unsafeRefine1 . f . PDP.unRefined
{-# INLINE unsafeMapRefine1 #-}

refined
   :: forall {kn} {kp} (p :: kn -> kp) (n :: kn) a
    . n @ a
   -> Proof (p n)
   -> a ? p
refined (Named a) = \_ -> MkRefined a
{-# INLINE refined #-}

refineS
   :: forall {kn} {kp} (p :: kn -> kp) a
    . (Description1 p)
   => a
   -> (forall (n :: kn). n @ a -> Maybe (Proof (p n)))
   -> Either String (a ? p)
refineS a f = name a $ \na ->
   maybe (Left (description1 @p "")) (Right . refined na) (f na)
{-# INLINE refineS #-}

refineF
   :: forall {kn} {kp} (p :: kn -> kp) a m
    . (Description1 p, MonadFail m)
   => a
   -> (forall (n :: kn). n @ a -> Maybe (Proof (p n)))
   -> m (a ? p)
refineF a f = either fail pure (refineS a f)
{-# INLINE refineF #-}

refineT
   :: forall {kn} {kp} (p :: kn -> kp) a m
    . (Description1 p, MonadThrow m)
   => a
   -> (forall (n :: kn). n @ a -> Maybe (Proof (p n)))
   -> m (a ? p)
refineT a f = either (throwM . Disproved) pure (refineS a f)
{-# INLINE refineT #-}

unsafeRefine
   :: forall {kn} {kp} (p :: kn -> kp) a
    . (Description1 p, HasCallStack)
   => a
   -> (forall (n :: kn). n @ a -> Maybe (Proof (p n)))
   -> a ? p
unsafeRefine a f = either error Prelude.id (refineS a f)
{-# INLINE unsafeRefine #-}

refine1S
   :: forall {kn} {kp} (p :: kn -> kp) a
    . (Prove1 p a, Description1 p)
   => a
   -> Either String (a ? p)
refine1S = \a -> name a $ \na -> refined na <$> prove1S na
{-# INLINE refine1S #-}

refine1T
   :: forall {kn} {kp} (p :: kn -> kp) a m
    . (Prove1 p a, Description1 p, MonadThrow m)
   => a
   -> m (a ? p)
refine1T = \a -> name a $ \na -> refined na <$> prove1T na
{-# INLINE refine1T #-}

refine1F
   :: forall {kn} {kp} (p :: kn -> kp) a m
    . (Prove1 p a, Description1 p, MonadFail m)
   => a
   -> m (a ? p)
refine1F = \a -> name a $ \na -> refined na <$> prove1F na
{-# INLINE refine1F #-}

unsafeRefine1
   :: forall {kn} {kp} (p :: kn -> kp) a
    . (Prove1 p a, Description1 p, HasCallStack)
   => a
   -> a ? p
unsafeRefine1 = either error Prelude.id . refine1S
{-# INLINE unsafeRefine1 #-}

mapRefined
   :: forall {kn} {kp} (p :: kn -> kp) a b m
    . (forall (n :: kn). n @ a -> Proof (p n) -> m (b ? p))
   -> a ? p
   -> m (b ? p)
mapRefined x = \f -> rename f x
{-# INLINE mapRefined #-}

rename
   :: forall {kn} {kp} (p :: kn -> kp) a b
    . a ? p
   -> (forall (n :: kn). n @ a -> Proof (p n) -> b)
   -> b
rename (Refined a) g = g (MkNamed a) axiom
{-# INLINE rename #-}

traverseRefined
   :: (Traversable t, Applicative f)
   => (forall n. n @ a -> Proof (p n) -> f b)
   -> t (a ? p)
   -> f (t b)
traverseRefined g = traverse (\r -> rename r g)
{-# INLINE traverseRefined #-}

forRefined
   :: (Traversable t, Applicative f)
   => t (a ? p)
   -> (forall n. n @ a -> Proof (p n) -> f b)
   -> f (t b)
forRefined t g = traverseRefined g t
{-# INLINE forRefined #-}

--------------------------------------------------------------------------------

-- | @x < y@, according to 'Ord'.
data LT y x

type LT :: y -> x -> Type

-- | @x == y@, according to 'Ord'.
data EQ y x

type EQ :: y -> x -> Type

-- | @x > y@, according to 'Ord'.
data GT y x

type GT :: y -> x -> Type

-- | @x /= y@, according to 'Ord'.
type NE y = OR1 (LT y) (GT y)

type NE :: y -> x -> Type

-- | @x <= y@, according to 'Ord'.
type LE y = OR1 (LT y) (EQ y)

type LE :: y -> x -> Type

-- | @x >= y@, according to 'Ord'.
type GE y = OR1 (GT y) (EQ y)

type GE :: y -> x -> Type

ltTrans :: Proof (LT a b --> LT b c --> LT a c)
ltTrans = axiom

ltAsym :: Proof (LT a b --> NOT (LT b a))
ltAsym = axiom

ltGT :: Proof (LT a b --> GT b a)
ltGT = axiom

notLT :: Proof (NOT (LT a b) --> GE a b)
notLT = axiom

eqTrans :: Proof (EQ a b --> EQ b c --> EQ a c)
eqTrans = axiom

eqNotNE :: Proof (EQ a b --> NOT (NE a b))
eqNotNE = axiom

eqSym :: Proof (EQ a b --> EQ b a)
eqSym = axiom

eqRefl :: Proof (EQ a a)
eqRefl = axiom

notEQ :: Proof (NOT (EQ a b) --> NE a b)
notEQ = axiom

ltNE :: Proof (LT a b --> NE a b)
ltNE = axiom

ltNotGE :: Proof (LT a b --> NOT (GE a b))
ltNotGE = axiom

gtNE :: Proof (GT a b --> NE a b)
gtNE = axiom

gtTrans :: Proof (GT a b --> GT b c --> GT a c)
gtTrans = axiom

gtAsym :: Proof (GT a b --> NOT (GT b a))
gtAsym = axiom

gtLT :: Proof (GT a b --> LT b a)
gtLT = axiom

gtNotLE :: Proof (GT a b --> NOT (LE a b))
gtNotLE = axiom

notGT :: Proof (NOT (GT a b) --> LE a b)
notGT = axiom

leTrans :: Proof (LE a b --> LE b c --> LE a c)
leTrans = axiom

leGE :: Proof (LE a b --> GE b a)
leGE = axiom

notLE :: Proof (NOT (LE a b) --> GT a b)
notLE = axiom

geTrans :: Proof (GE a b --> GE b c --> GE a c)
geTrans = axiom

geLE :: Proof (GE a b --> LE b a)
geLE = axiom

notGE :: Proof (NOT (GE a b) -> LT a b)
notGE = axiom

neSym :: Proof (NE a b --> NE b a)
neSym = axiom

lt
   :: (Ord x)
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (LT l r))) (Proof (LT l r))
lt fa fb = \(Named la) (Named rb) ->
   if fb rb < fa la then Right axiom else Left axiom

eq
   :: (Eq x)
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (EQ l r))) (Proof (EQ l r))
eq fa fb = \(Named la) (Named rb) ->
   if fb rb == fa la then Right axiom else Left axiom

gt
   :: (Ord x)
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (GT l r))) (Proof (GT l r))
gt fa fb = \(Named la) (Named rb) ->
   if fb rb > fa la then Right axiom else Left axiom

le
   :: (Ord x)
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (LE l r))) (Proof (LE l r))
le fa fb = \l r ->
   either
      (Right . mp notGT)
      (Left . mp gtNotLE)
      (gt fa fb l r)

ne
   :: (Eq x)
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (NE l r))) (Proof (NE l r))
ne fa fb = \l r ->
   either
      (Right . mp notEQ)
      (Left . mp eqNotNE)
      (eq fa fb l r)

ge
   :: (Ord x)
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (GE l r))) (Proof (GE l r))
ge fa fb = \l r ->
   either
      (Right . mp notLT)
      (Left . mp ltNotGE)
      (lt fa fb l r)

--------------------------------------------------------------------------------

class Prove (p :: k) where
   prove' :: Either (Proof (NOT p)) (Proof p)

prove :: forall {k} (p :: k). (Prove p) => Either (Proof (NOT p)) (Proof p)
prove = prove' @k @p

instance (Prove p) => Prove (NOT p) where
   prove' = case prove @p of
      Right _ -> Left axiom
      Left _ -> Right axiom

instance forall p q na. (Prove (AND (p na) (q na))) => Prove (AND1 p q na) where
   prove' = case prove @(AND (p na) (q na)) of
      Right _ -> Right axiom
      Left _ -> Left axiom

instance forall p q. (Prove p, Prove q) => Prove (AND p q) where
   prove' = case (prove @p, prove @q) of
      (Right _, Right _) -> Right axiom
      _ -> Left axiom

instance forall p q na. (Prove (OR (p na) (q na))) => Prove (OR1 p q na) where
   prove' = case prove @(OR (p na) (q na)) of
      Right _ -> Right axiom
      Left _ -> Left axiom

instance forall p q. (Prove p, Prove q) => Prove (OR p q) where
   prove' = case (prove @p, prove @q) of
      (Right _, _) -> Right axiom
      (_, Right _) -> Right axiom
      _ -> Left axiom

-------------------------------------------------------------------------------

description1 :: forall {kn} {kp} (p :: kn -> kp). (Description1 p) => ShowS
description1 = description1' @kn @kp @p
{-# INLINE description1 #-}

class Description1 (p :: kn -> kp) where
   description1' :: ShowS

instance forall p. (Description1 p) => Description1 (NOT1 p) where
   description1' = showString "not (" . description1 @p . showChar ')'

instance
   forall l r
    . (Description1 l, Description1 r)
   => Description1 (AND1 l r)
   where
   description1' =
      showChar '('
         . description1 @l
         . showString ") and ("
         . description1 @r
         . showChar ')'

instance
   forall l r
    . (Description1 l, Description1 r)
   => Description1 (OR1 l r)
   where
   description1' =
      showChar '('
         . description1 @l
         . showString ") or ("
         . description1 @r
         . showChar ')'

instance
   {-# OVERLAPPABLE #-}
   forall k n
    . (SingKind k, SingI n, Show (Demote k))
   => Description1 (GT (n :: k))
   where
   description1' = showString "more than " . showsPrec appPrec1 (demote @n)

instance
   {-# OVERLAPPABLE #-}
   forall k n
    . (SingKind k, SingI n, Show (Demote k))
   => Description1 (LT (n :: k))
   where
   description1' = showString "less than " . showsPrec appPrec1 (demote @n)

instance
   {-# OVERLAPPABLE #-}
   forall k n
    . (SingKind k, SingI n, Show (Demote k))
   => Description1 (EQ (n :: k))
   where
   description1' = showString "equal to " . showsPrec appPrec1 (demote @n)

--------------------------------------------------------------------------------

class Prove1 (p :: kn -> kpn) a where
   prove1E' :: n @ a -> Either (Proof (NOT (p n))) (Proof (p n))

prove1E
   :: forall {kn} {kpn} (p :: kn -> kpn) a (n :: kn)
    . (Prove1 p a)
   => n @ a
   -> Either (Proof (NOT (p n))) (Proof (p n))
prove1E = prove1E'
{-# INLINE prove1E #-}

prove1T
   :: forall {kn} {kpn} (p :: kn -> kpn) a (n :: kn) m
    . (Prove1 p a, Description1 p, MonadThrow m)
   => n @ a
   -> m (Proof (p n))
prove1T = either (throwM . Disproved) pure . prove1S
{-# INLINE prove1T #-}

prove1F
   :: forall {kn} {kpn} (p :: kn -> kpn) a (n :: kn) m
    . (Prove1 p a, Description1 p, MonadFail m)
   => n @ a
   -> m (Proof (p n))
prove1F = either fail pure . prove1S
{-# INLINE prove1F #-}

prove1S
   :: forall {kn} {kpn} (p :: kn -> kpn) a (n :: kn)
    . (Prove1 p a, Description1 p)
   => n @ a
   -> Either String (Proof (p n))
prove1S = first (\_ -> description1 @p "") . prove1E
{-# INLINE prove1S #-}

instance (Prove1 p a) => Prove1 (NOT1 p) a where
   {-# INLINE prove1E' #-}
   prove1E' = \na -> case prove1E @p @a na of
      Left _ -> Right axiom
      _ -> Left axiom

instance (Prove1 f a, Prove1 g a) => Prove1 (AND1 f g) a where
   {-# INLINE prove1E' #-}
   prove1E' = \na -> case (prove1E @f @a na, prove1E @g @a na) of
      (Right _, Right _) -> Right axiom
      _ -> Left axiom

instance (Prove1 f a, Prove1 g a) => Prove1 (OR1 f g) a where
   {-# INLINE prove1E' #-}
   prove1E' = \na -> case (prove1E @f @a na, prove1E @g @a na) of
      (Right _, _) -> Right axiom
      (_, Right _) -> Right axiom
      _ -> Left axiom

instance (Prove1 p a) => Prove1 p (Tagged x a) where
   {-# INLINE prove1E' #-}
   prove1E' = prove1E' . unsafeMapNamed unTagged

--------------------------------------------------------------------------------

instance (Ord x) => Prove2 LT x x where
   {-# INLINE prove2E' #-}
   prove2E' = \cases
      nz na
         | unNamed na < unNamed nz -> Right axiom
         | otherwise -> Left axiom

instance (Ord x) => Prove2 GT x x where
   {-# INLINE prove2E' #-}
   prove2E' = \cases
      na nz
         | unNamed nz > unNamed na -> Right axiom
         | otherwise -> Left axiom

instance (Ord x) => Prove2 EQ x x where
   {-# INLINE prove2E' #-}
   prove2E' = \cases
      na nb
         | unNamed nb == unNamed na -> Right axiom
         | otherwise -> Left axiom

instance
   {-# OVERLAPPABLE #-}
   forall ka kb kp (p :: ka -> kb -> kp) (na :: ka) b
    . (SingKind ka, SingI na, Prove2 p (Demote ka) b)
   => Prove1 (p na) b
   where
   prove1E' = prove2E (namedDemote @na)
   {-# INLINE prove1E' #-}

namedDemote :: forall {k} (n :: k). (SingKind k, SingI n) => n @ Demote k
namedDemote = unsafeNamed (demote @n)
{-# INLINE namedDemote #-}

class Prove2 (p :: ka -> kb -> kpab) a b where
   prove2E'
      :: na @ a
      -> nb @ b
      -> Either (Proof (NOT (p na nb))) (Proof (p na nb))

prove2E
   :: forall {ka} {kb} {kpab} (p :: ka -> kb -> kpab) a b na nb
    . (Prove2 p a b)
   => na @ a
   -> nb @ b
   -> Either (Proof (NOT (p na nb))) (Proof (p na nb))
prove2E = prove2E'
{-# INLINE prove2E #-}

prove2S
   :: forall {ka} {kb} {kpab} (p :: ka -> kb -> kpab) a b na nb
    . (Prove2 p a b, Description1 p)
   => na @ a
   -> nb @ b
   -> Either String (Proof (p na nb))
prove2S = \a b -> first (\_ -> description1 @p "") (prove2S a b)
{-# INLINE prove2S #-}

prove2F
   :: forall {ka} {kb} {kpab} (p :: ka -> kb -> kpab) a b na nb m
    . (Prove2 p a b, Description1 p, MonadFail m)
   => na @ a
   -> nb @ b
   -> m (Proof (p na nb))
prove2F = \a b -> either fail pure (prove2S a b)
{-# INLINE prove2F #-}

prove2T
   :: forall {ka} {kb} {kpab} (p :: ka -> kb -> kpab) a b na nb m
    . (Prove2 p a b, Description1 p, MonadThrow m)
   => na @ a
   -> nb @ b
   -> m (Proof (p na nb))
prove2T = \a b -> either (throwM . Disproved) pure (prove2S a b)
{-# INLINE prove2T #-}

instance (Prove2 p a b) => Prove2 p (Tagged x a) (Tagged y b) where
   {-# INLINE prove2E' #-}
   prove2E' = \nta ntb ->
      prove2E'
         (unsafeMapNamed unTagged nta)
         (unsafeMapNamed unTagged ntb)

--------------------------------------------------------------------------------

instance
   (Csv.FromField a, Prove1 p a, Description1 p)
   => Csv.FromField (a ? p)
   where
   parseField = Csv.parseField >=> refine1F
   {-# INLINE parseField #-}

instance
   (Csv.FromRecord a, Prove1 p a, Description1 p)
   => Csv.FromRecord (a ? p)
   where
   parseRecord = Csv.parseRecord >=> refine1F
   {-# INLINE parseRecord #-}

--------------------------------------------------------------------------------

instance
   (Ae.FromJSON a, Prove1 p a, Description1 p)
   => Ae.FromJSON (a ? p)
   where
   parseJSON = \v -> Ae.parseJSON v >>= refine1F
   {-# INLINE parseJSON #-}

--------------------------------------------------------------------------------

instance (Bin.Binary a, Prove1 p a, Description1 p) => Bin.Binary (a ? p) where
   put = \(Refined a) -> Bin.put a
   {-# INLINE put #-}
   get = Bin.get >>= refine1F
   {-# INLINE get #-}

--------------------------------------------------------------------------------

#define INST_VIA(D, U, f) \
  instance Prove2 p (U) (U) => Prove2 p (D) (U) where { \
    prove2E' = (\g -> \nta ntb -> prove2E' (unsafeMapNamed g nta) ntb) \
               ((f) :: (D) -> (U)); \
    {-# INLINE prove2E' #-}; \
  }; \
  instance Prove2 p (U) (U) => Prove2 p (U) (D) where { \
    prove2E' = (\g -> \nta ntb -> prove2E' nta (unsafeMapNamed g ntb)) \
               ((f) :: (D) -> (U)); \
    {-# INLINE prove2E' #-}; \
  };

INST_VIA (Int, Int64, fromIntegral)
INST_VIA (Int, Integer, fromIntegral)
INST_VIA (Int, Rational, fromIntegral)
INST_VIA (Int, Scientific, fromIntegral)
INST_VIA (Int, Fixed E0, fromIntegral)
INST_VIA (Int, Fixed E1, fromIntegral)
INST_VIA (Int, Fixed E2, fromIntegral)
INST_VIA (Int, Fixed E3, fromIntegral)
INST_VIA (Int, Fixed E6, fromIntegral)
INST_VIA (Int, Fixed E9, fromIntegral)
INST_VIA (Int, Fixed E12, fromIntegral)

INST_VIA (Int8, Int16, fromIntegral)
INST_VIA (Int8, Int32, fromIntegral)
INST_VIA (Int8, Int64, fromIntegral)
INST_VIA (Int8, Integer, fromIntegral)
INST_VIA (Int8, Float, fromIntegral)
INST_VIA (Int8, Double, fromIntegral)
INST_VIA (Int8, Rational, fromIntegral)
INST_VIA (Int8, Scientific, fromIntegral)
INST_VIA (Int8, Fixed E0, fromIntegral)
INST_VIA (Int8, Fixed E1, fromIntegral)
INST_VIA (Int8, Fixed E2, fromIntegral)
INST_VIA (Int8, Fixed E3, fromIntegral)
INST_VIA (Int8, Fixed E6, fromIntegral)
INST_VIA (Int8, Fixed E9, fromIntegral)
INST_VIA (Int8, Fixed E12, fromIntegral)

INST_VIA (Int16, Int32, fromIntegral)
INST_VIA (Int16, Int64, fromIntegral)
INST_VIA (Int16, Integer, fromIntegral)
INST_VIA (Int16, Float, fromIntegral)
INST_VIA (Int16, Double, fromIntegral)
INST_VIA (Int16, Rational, fromIntegral)
INST_VIA (Int16, Scientific, fromIntegral)
INST_VIA (Int16, Fixed E0, fromIntegral)
INST_VIA (Int16, Fixed E1, fromIntegral)
INST_VIA (Int16, Fixed E2, fromIntegral)
INST_VIA (Int16, Fixed E3, fromIntegral)
INST_VIA (Int16, Fixed E6, fromIntegral)
INST_VIA (Int16, Fixed E9, fromIntegral)
INST_VIA (Int16, Fixed E12, fromIntegral)

INST_VIA (Int32, Int64, fromIntegral)
INST_VIA (Int32, Integer, fromIntegral)
INST_VIA (Int32, Double, fromIntegral)
INST_VIA (Int32, Rational, fromIntegral)
INST_VIA (Int32, Scientific, fromIntegral)
INST_VIA (Int32, Fixed E0, fromIntegral)
INST_VIA (Int32, Fixed E1, fromIntegral)
INST_VIA (Int32, Fixed E2, fromIntegral)
INST_VIA (Int32, Fixed E3, fromIntegral)
INST_VIA (Int32, Fixed E6, fromIntegral)
INST_VIA (Int32, Fixed E9, fromIntegral)
INST_VIA (Int32, Fixed E12, fromIntegral)

INST_VIA (Int64, Integer, fromIntegral)
INST_VIA (Int64, Rational, fromIntegral)
INST_VIA (Int64, Scientific, fromIntegral)
INST_VIA (Int64, Fixed E0, fromIntegral)
INST_VIA (Int64, Fixed E1, fromIntegral)
INST_VIA (Int64, Fixed E2, fromIntegral)
INST_VIA (Int64, Fixed E3, fromIntegral)
INST_VIA (Int64, Fixed E6, fromIntegral)
INST_VIA (Int64, Fixed E9, fromIntegral)
INST_VIA (Int64, Fixed E12, fromIntegral)

INST_VIA (Word, Integer, fromIntegral)
INST_VIA (Word, Natural, fromIntegral)
INST_VIA (Word, Word64, fromIntegral)
INST_VIA (Word, Rational, fromIntegral)
INST_VIA (Word, Scientific, fromIntegral)
INST_VIA (Word, Fixed E0, fromIntegral)
INST_VIA (Word, Fixed E1, fromIntegral)
INST_VIA (Word, Fixed E2, fromIntegral)
INST_VIA (Word, Fixed E3, fromIntegral)
INST_VIA (Word, Fixed E6, fromIntegral)
INST_VIA (Word, Fixed E9, fromIntegral)
INST_VIA (Word, Fixed E12, fromIntegral)

INST_VIA (Word8, Integer, fromIntegral)
INST_VIA (Word8, Natural, fromIntegral)
INST_VIA (Word8, Word16, fromIntegral)
INST_VIA (Word8, Word32, fromIntegral)
INST_VIA (Word8, Word64, fromIntegral)
INST_VIA (Word8, Float, fromIntegral)
INST_VIA (Word8, Double, fromIntegral)
INST_VIA (Word8, Rational, fromIntegral)
INST_VIA (Word8, Scientific, fromIntegral)
INST_VIA (Word8, Fixed E0, fromIntegral)
INST_VIA (Word8, Fixed E1, fromIntegral)
INST_VIA (Word8, Fixed E2, fromIntegral)
INST_VIA (Word8, Fixed E3, fromIntegral)
INST_VIA (Word8, Fixed E6, fromIntegral)
INST_VIA (Word8, Fixed E9, fromIntegral)
INST_VIA (Word8, Fixed E12, fromIntegral)

INST_VIA (Word16, Integer, fromIntegral)
INST_VIA (Word16, Natural, fromIntegral)
INST_VIA (Word16, Word32, fromIntegral)
INST_VIA (Word16, Word64, fromIntegral)
INST_VIA (Word16, Float, fromIntegral)
INST_VIA (Word16, Double, fromIntegral)
INST_VIA (Word16, Rational, fromIntegral)
INST_VIA (Word16, Scientific, fromIntegral)
INST_VIA (Word16, Fixed E0, fromIntegral)
INST_VIA (Word16, Fixed E1, fromIntegral)
INST_VIA (Word16, Fixed E2, fromIntegral)
INST_VIA (Word16, Fixed E3, fromIntegral)
INST_VIA (Word16, Fixed E6, fromIntegral)
INST_VIA (Word16, Fixed E9, fromIntegral)
INST_VIA (Word16, Fixed E12, fromIntegral)

INST_VIA (Word32, Integer, fromIntegral)
INST_VIA (Word32, Natural, fromIntegral)
INST_VIA (Word32, Word64, fromIntegral)
INST_VIA (Word32, Double, fromIntegral)
INST_VIA (Word32, Rational, fromIntegral)
INST_VIA (Word32, Scientific, fromIntegral)
INST_VIA (Word32, Fixed E0, fromIntegral)
INST_VIA (Word32, Fixed E1, fromIntegral)
INST_VIA (Word32, Fixed E2, fromIntegral)
INST_VIA (Word32, Fixed E3, fromIntegral)
INST_VIA (Word32, Fixed E6, fromIntegral)
INST_VIA (Word32, Fixed E9, fromIntegral)
INST_VIA (Word32, Fixed E12, fromIntegral)

INST_VIA (Word64, Integer, fromIntegral)
INST_VIA (Word64, Natural, fromIntegral)
INST_VIA (Word64, Rational, fromIntegral)
INST_VIA (Word64, Scientific, fromIntegral)
INST_VIA (Word64, Fixed E0, fromIntegral)
INST_VIA (Word64, Fixed E1, fromIntegral)
INST_VIA (Word64, Fixed E2, fromIntegral)
INST_VIA (Word64, Fixed E3, fromIntegral)
INST_VIA (Word64, Fixed E6, fromIntegral)
INST_VIA (Word64, Fixed E9, fromIntegral)
INST_VIA (Word64, Fixed E12, fromIntegral)

INST_VIA (Float, Double, realToFrac)

#if WORD_SIZE_IN_BITS == 64
INST_VIA(Word64, Word, fromIntegral)
INST_VIA(Int64, Int, fromIntegral)
#elif WORD_SIZE_IN_BITS == 32
INST_VIA(Int, Double, fromIntegral)
INST_VIA(Int, Int32, fromIntegral)
INST_VIA(Word, Word32, fromIntegral)
INST_VIA(Word, Double, fromIntegral)
#endif

INST_VIA (Natural, Integer, fromIntegral)
INST_VIA (Natural, Rational, fromIntegral)
INST_VIA (Natural, Scientific, fromIntegral)

INST_VIA (Integer, Rational, fromIntegral)
INST_VIA (Integer, Scientific, fromIntegral)

INST_VIA (Natural, Fixed E0, fromIntegral)
INST_VIA (Natural, Fixed E1, fromIntegral)
INST_VIA (Natural, Fixed E2, fromIntegral)
INST_VIA (Natural, Fixed E3, fromIntegral)
INST_VIA (Natural, Fixed E6, fromIntegral)
INST_VIA (Natural, Fixed E9, fromIntegral)
INST_VIA (Natural, Fixed E12, fromIntegral)
INST_VIA (Integer, Fixed E0, fromIntegral)
INST_VIA (Integer, Fixed E1, fromIntegral)
INST_VIA (Integer, Fixed E2, fromIntegral)
INST_VIA (Integer, Fixed E3, fromIntegral)
INST_VIA (Integer, Fixed E6, fromIntegral)
INST_VIA (Integer, Fixed E9, fromIntegral)
INST_VIA (Integer, Fixed E12, fromIntegral)
INST_VIA (Fixed E0, Fixed E1, realToFrac)
INST_VIA (Fixed E0, Fixed E2, realToFrac)
INST_VIA (Fixed E0, Fixed E3, realToFrac)
INST_VIA (Fixed E0, Fixed E6, realToFrac)
INST_VIA (Fixed E0, Fixed E9, realToFrac)
INST_VIA (Fixed E0, Fixed E12, realToFrac)
INST_VIA (Fixed E1, Fixed E2, realToFrac)
INST_VIA (Fixed E1, Fixed E3, realToFrac)
INST_VIA (Fixed E1, Fixed E6, realToFrac)
INST_VIA (Fixed E1, Fixed E9, realToFrac)
INST_VIA (Fixed E1, Fixed E12, realToFrac)
INST_VIA (Fixed E2, Fixed E3, realToFrac)
INST_VIA (Fixed E2, Fixed E6, realToFrac)
INST_VIA (Fixed E2, Fixed E9, realToFrac)
INST_VIA (Fixed E2, Fixed E12, realToFrac)
INST_VIA (Fixed E3, Fixed E6, realToFrac)
INST_VIA (Fixed E3, Fixed E9, realToFrac)
INST_VIA (Fixed E3, Fixed E12, realToFrac)
INST_VIA (Fixed E6, Fixed E9, realToFrac)
INST_VIA (Fixed E6, Fixed E12, realToFrac)
INST_VIA (Fixed E9, Fixed E12, realToFrac)

INST_VIA (Natural, Time.NominalDiffTime, fromIntegral)
INST_VIA (Word, Time.NominalDiffTime, fromIntegral)
INST_VIA (Word8, Time.NominalDiffTime, fromIntegral)
INST_VIA (Word16, Time.NominalDiffTime, fromIntegral)
INST_VIA (Word32, Time.NominalDiffTime, fromIntegral)
INST_VIA (Word64, Time.NominalDiffTime, fromIntegral)
INST_VIA (Integer, Time.NominalDiffTime, fromIntegral)
INST_VIA (Int, Time.NominalDiffTime, fromIntegral)
INST_VIA (Int8, Time.NominalDiffTime, fromIntegral)
INST_VIA (Int16, Time.NominalDiffTime, fromIntegral)
INST_VIA (Int32, Time.NominalDiffTime, fromIntegral)
INST_VIA (Int64, Time.NominalDiffTime, fromIntegral)
INST_VIA (Fixed E0, Time.NominalDiffTime, realToFrac)
INST_VIA (Fixed E1, Time.NominalDiffTime, realToFrac)
INST_VIA (Fixed E2, Time.NominalDiffTime, realToFrac)
INST_VIA (Fixed E3, Time.NominalDiffTime, realToFrac)
INST_VIA (Fixed E6, Time.NominalDiffTime, realToFrac)
INST_VIA (Fixed E9, Time.NominalDiffTime, realToFrac)
INST_VIA (Fixed E12, Time.NominalDiffTime, realToFrac)

INST_VIA (Natural, Time.DiffTime, fromIntegral)
INST_VIA (Word, Time.DiffTime, fromIntegral)
INST_VIA (Word8, Time.DiffTime, fromIntegral)
INST_VIA (Word16, Time.DiffTime, fromIntegral)
INST_VIA (Word32, Time.DiffTime, fromIntegral)
INST_VIA (Word64, Time.DiffTime, fromIntegral)
INST_VIA (Integer, Time.DiffTime, fromIntegral)
INST_VIA (Int, Time.DiffTime, fromIntegral)
INST_VIA (Int8, Time.DiffTime, fromIntegral)
INST_VIA (Int16, Time.DiffTime, fromIntegral)
INST_VIA (Int32, Time.DiffTime, fromIntegral)
INST_VIA (Int64, Time.DiffTime, fromIntegral)
INST_VIA (Fixed E0, Time.DiffTime, realToFrac)
INST_VIA (Fixed E1, Time.DiffTime, realToFrac)
INST_VIA (Fixed E2, Time.DiffTime, realToFrac)
INST_VIA (Fixed E3, Time.DiffTime, realToFrac)
INST_VIA (Fixed E6, Time.DiffTime, realToFrac)
INST_VIA (Fixed E9, Time.DiffTime, realToFrac)
INST_VIA (Fixed E12, Time.DiffTime, realToFrac)

INST_VIA (Time.DiffTime, Rational, toRational)
INST_VIA (Time.DiffTime, Scientific, realToFrac)

INST_VIA (Time.NominalDiffTime, Rational, toRational)
INST_VIA (Time.NominalDiffTime, Scientific, realToFrac)

INST_VIA (Fixed E0, Rational, toRational)
INST_VIA (Fixed E1, Rational, toRational)
INST_VIA (Fixed E2, Rational, toRational)
INST_VIA (Fixed E3, Rational, toRational)
INST_VIA (Fixed E6, Rational, toRational)
INST_VIA (Fixed E9, Rational, toRational)
INST_VIA (Fixed E12, Rational, toRational)

INST_VIA (Fixed E0, Scientific, realToFrac)
INST_VIA (Fixed E1, Scientific, realToFrac)
INST_VIA (Fixed E2, Scientific, realToFrac)
INST_VIA (Fixed E3, Scientific, realToFrac)
INST_VIA (Fixed E6, Scientific, realToFrac)
INST_VIA (Fixed E9, Scientific, realToFrac)
INST_VIA (Fixed E12, Scientific, realToFrac)
