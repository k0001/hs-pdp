{-# LANGUAGE UndecidableInstances #-}

module PDP
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

  , Prove1(..)
  , prove1S
  , prove1S1
  , prove1E

  , Prove(..)
  , proveE

  , LT, lt
  , LE, le
  , EQ, eq
  , GE, ge
  , GT, gt
  , NE, ne
  , neSym
  , notGE
  , geLE
  , geTrans
  , notLE
  , leGE
  , leTrans
  , notGT
  , gtLT
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

  , Named
  , pattern Named
  , type (@)
  , unsafeNamed
  , unNamed
  , name

  , NamedI(..)
  , unNamedI

  , Refined
  , pattern Refined
  , type (?)
  , unsafeRefined
  , unRefined
  , refine
  , rename
  , forRefined
  , traverseRefined

  ) where

import Control.Applicative
import Control.Monad
import Data.Aeson qualified as Ae
import Data.Coerce
import Data.Binary qualified as Bin
import Data.Singletons
import Data.Kind (Type)
import GHC.Exts (withDict)
import GHC.TypeLits (type (<=))
import GHC.TypeNats (KnownNat)
import KindInteger qualified as KI
import KindRational qualified as KR
import Numeric.Natural
import GHC.Show (appPrec1)

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
  deriving newtype (Eq, Ord, Show, Ae.ToJSON)

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

name :: forall a b. a -> (forall n. NamedI n a => n @ a -> b) -> b
name a f = withNamed a $ \na -> withNamedI na (f na)

withNamed :: forall a b. a -> (forall n. n @ a -> b) -> b
withNamed a f = f (MkNamed a)
{-# NOINLINE withNamed #-}

withNamedI :: forall n a b. n @ a -> (NamedI n a => b) -> b
withNamedI na b = withDict @(NamedI n a) @(n @ a) na b
{-# NOINLINE withNamedI #-}

--------------------------------------------------------------------------------

newtype Refined (a :: Type) (p :: Type -> Type) = MkRefined a
  deriving newtype (Eq, Ord, Show, Ae.ToJSON)

type role Refined representational nominal
type (?) = Refined

unsafeRefined :: forall p a. a -> a ? p
unsafeRefined = coerce
{-# INLINE unsafeRefined #-}

unRefined :: a ? p -> a
unRefined = coerce
{-# INLINE unRefined #-}

pattern Refined :: a -> a ? p
pattern Refined a <- (unRefined -> a)
{-# COMPLETE Refined #-}

refine :: n @ a -> Proof (p (n @ a)) -> a ? p
refine (Named a) _ = MkRefined a
{-# INLINE refine #-}

rename :: a ? p -> (forall n. n @ a -> Proof (p (n @ a)) -> b) -> b
rename (Refined a) g = g (MkNamed a) axiom
{-# NOINLINE rename #-}

traverseRefined
  :: (Traversable t, Applicative f)
  => (forall n. n @ a -> Proof (p (n @ a)) -> f b)
  -> t (a ? p)
  -> f (t b)
traverseRefined g = traverse (\r -> rename r g)
{-# INLINE traverseRefined #-}

forRefined
  :: (Traversable t, Applicative f)
  => t (a ? p)
  -> (forall n. n @ a -> Proof (p (n @ a)) -> f b)
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

eqSym :: Proof (EQ a b --> EQ b a)
eqSym = axiom

eqRefl :: Proof (EQ a a)
eqRefl = axiom

notEQ :: Proof (NOT (EQ a b) --> NE a b)
notEQ = axiom

gtTrans :: Proof (GT a b --> GT b c --> GT a c)
gtTrans = axiom

gtAsym :: Proof (GT a b --> NOT (GT b a))
gtAsym = axiom

gtLT :: Proof (GT a b --> LT b a)
gtLT = axiom

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

lt :: Ord a => y @ a -> x @ a
   -> Either (Proof (NOT (LT y x))) (Proof (LT y x))
lt (Named y) (Named x) = if x < y then Right axiom else Left axiom

eq :: Ord a => y @ a -> x @ a
   -> Either (Proof (NOT (EQ y x))) (Proof (EQ y x))
eq (Named y) (Named x) = if x == y then Right axiom else Left axiom

gt :: Ord a => y @ a -> x @ a
   -> Either (Proof (NOT (GT y x))) (Proof (GT y x))
gt (Named y) (Named x) = if x > y then Right axiom else Left axiom

le :: Ord a => y @ a -> x @ a
   -> Either (Proof (NOT (LE y x))) (Proof (LE y x))
le (Named y) (Named x) = if x <= y then Right axiom else Left axiom

ne :: Ord a => y @ a -> x @ a
   -> Either (Proof (NOT (NE y x))) (Proof (NE y x))
ne (Named y) (Named x) = if x /= y then Right axiom else Left axiom

ge :: Ord a => y @ a -> x @ a
   -> Either (Proof (NOT (GE y x))) (Proof (GE y x))
ge (Named y) (Named x) = if x >= y then Right axiom else Left axiom

--------------------------------------------------------------------------------

class Prove (p :: Type) where
  prove :: Maybe (Proof p)

proveE :: forall p. Prove p => Either (Proof (NOT p)) (Proof p)
proveE = maybe (Left axiom) Right prove

instance Prove p => Prove (NOT p) where
  prove | Nothing <- prove @p = Just axiom
        | otherwise = Nothing

instance Prove (AND (p na) (q na)) => Prove (AND1 p q na) where
  prove = fmap (and1 $*) prove

instance (Prove p, Prove q) => Prove (AND p q) where
  prove = do p <- prove @p
             q <- prove @q
             Just (PDP.and $* p $* q)

instance Prove (OR (p na) (q na)) => Prove (OR1 p q na) where
  prove = mp or1 <$> prove

instance (Prove p, Prove q) => Prove (OR p q) where
  prove = fmap (mp left ) (prove @p) <|>
          fmap (mp right) (prove @q)

instance forall z a t. (Ord t, NamedI z t, NamedI a t)
  => Prove (LT (z @ t) (a @ t)) where
  prove | unNamedI @a @t <  unNamedI @z @t = Just axiom
        | otherwise = Nothing

instance forall x y t. (Ord t, NamedI x t, NamedI y t)
  => Prove (EQ (x @ t) (y @ t)) where
  prove | unNamedI @y @t == unNamedI @x @t = Just axiom
        | otherwise = Nothing

instance forall a z t. (Ord t, NamedI a t, NamedI z t)
  => Prove (GT (a @ t) (z @ t)) where
  prove | unNamedI @z @t >  unNamedI @a @t = Just axiom
        | otherwise = Nothing

--------------------------------------------------------------------------------

class Description1 (f :: Type -> Type) where
  description1 :: ShowS

instance forall f. Description1 f => Description1 (NOT1 f) where
  description1 = showString "not (" . description1 @f . showChar ')'

instance forall l r. (Description1 l, Description1 r) => Description1 (AND1 l r) where
  description1 = showChar '(' . description1 @l . showString ") and ("
               . description1 @r . showChar ')'

instance forall l r. (Description1 l, Description1 r) => Description1 (OR1 l r) where
  description1 = showChar '(' . description1 @l . showString ") or ("
               . description1 @r . showChar ')'

instance {-# OVERLAPPABLE #-} forall a t.
  (NamedI a t, Show t) => Description1 (GT (a @ t)) where
  description1 = showString "more than " . showsPrec appPrec1 (unNamedI @a @t)

instance {-# OVERLAPPABLE #-} forall z t.
  (NamedI z t, Show t) => Description1 (LT (z @ t)) where
  description1 = showString "less than " . showsPrec appPrec1 (unNamedI @z @t)

instance {-# OVERLAPPABLE #-} forall y t.
  (NamedI y t, Show t) => Description1 (EQ (y @ t)) where
  description1 = showString "equal to " . showsPrec appPrec1 (unNamedI @y @t)

--------------------------------------------------------------------------------

class Prove1 (f :: Type -> Type) (a :: Type) where
  prove1 :: n @ a -> Maybe (Proof (f (n @ a)))

prove1E :: forall f a n
        .  Prove1 f a
        => n @ a
        -> Either (Proof (NOT (f (n @ a)))) (Proof (f (n @ a)))
prove1E = maybe (Left axiom) Right . prove1

prove1S :: forall f a n
        .  (Prove1 f a, Description1 f, Show a)
        => n @ a
        -> Either String (Proof (f (n @ a)))
prove1S na = case prove1 na of
  Just p  -> Right p
  Nothing -> Left $ (showsPrec appPrec1 (unNamed na) .
                     showString " doesn't satisfy (" .
                     description1 @f . showChar ')') ""

prove1S1 :: forall f a n
         .  (Prove1 f a, Description1 f)
         => n @ a
         -> Either String (Proof (f (n @ a)))
prove1S1 = maybe (Left (description1 @f "")) Right . prove1

instance Prove1 f a => Prove1 (NOT1 f) a where
  prove1 na | Nothing <- prove1 @f @a na = Just axiom
            | otherwise                  = Nothing

instance (Prove1 f a, Prove1 g a) => Prove1 (AND1 f g) a where
  prove1 na = do fna <- prove1 @f @a na
                 gna <- prove1 @g @a na
                 Just (and1 $* (PDP.and $* fna $* gna))

instance (Prove1 f a, Prove1 g a) => Prove1 (OR1 f g) a where
  prove1 na = fmap (rmap $* or1 $* left  $*) (prove1 @f @a na) <|>
              fmap (rmap $* or1 $* right $*) (prove1 @g @a na)

instance forall z t. (Ord t, NamedI z t) => Prove1 (LT (z @ t)) t where
  prove1 na | unNamed na < unNamedI @z @t = Just axiom
            | otherwise = Nothing

instance forall x t. (Ord t, NamedI x t) => Prove1 (EQ (x @ t)) t where
  prove1 ny | unNamed ny == unNamedI @x @t = Just axiom
            | otherwise = Nothing

instance forall a t. (Ord t, NamedI a t) => Prove1 (GT (a @ t)) t where
  prove1 nz | unNamed nz > unNamedI @a @t = Just axiom
            | otherwise = Nothing

--------------------------------------------------------------------------------

class NamedI n a where
  namedI :: n @ a

unNamedI :: forall n a. NamedI n a => a
unNamedI = unNamed (namedI @n @a)
{-# INLINE unNamedI #-}

instance {-# OVERLAPPABLE #-}
  forall k (n :: k) a. (SingKind k, SingI n, a ~ Demote k)
  => NamedI n a where
  namedI = unsafeNamed (demote @n)

instance forall n. KnownNat n => NamedI n Integer where
  namedI = unsafeNamed (fromIntegral (demote @n))

instance forall n. KnownNat n => NamedI n Rational where
  namedI = unsafeNamed (fromIntegral (demote @n))

instance forall n. (KI.KnownInteger n, KI.FromNatural 0 <= n)
  => NamedI n Natural where
  namedI = unsafeNamed (demote @(KI.Abs n))

instance forall n. KI.KnownInteger n => NamedI n Rational where
  namedI = unsafeNamed (fromIntegral (demote @n))

instance forall n. (KR.KnownRational n, KR.Den n ~ 1, KI.FromNatural 0 <= KR.Num n)
  => NamedI n Natural where
  namedI = unsafeNamed (demote @(KI.Abs (KR.Num n)))

instance forall n. (KR.KnownRational n, KR.Den n ~ 1)
  => NamedI n Integer where
  namedI = unsafeNamed (demote @(KR.Num n))

--------------------------------------------------------------------------------

instance (Show a, Ae.FromJSON a, Prove1 p a, Description1 p)
  => Ae.FromJSON (a ? p) where
  parseJSON = Ae.parseJSON >=> \a ->
              name a $ \(na :: n @ a) ->
              either fail (pure . refine na) (prove1S na)

instance (Show a, Bin.Binary a, Prove1 p a, Description1 p)
  => Bin.Binary (a ? p) where
  put = Bin.put . unRefined
  get = Bin.get >>= \a ->
        name a $ \(na :: n @ a) ->
        either fail (pure . refine na) (prove1S na)


