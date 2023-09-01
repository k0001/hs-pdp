{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

module PDP {--
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
  , prove1E
  , prove1S
  , prove1S1
  , unsafeProve1S
  , unsafeProve1S1

  , Prove(..)

  , Description1(..)

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

  , Named
  , pattern Named
  , type (@)
  , unsafeNamed
  , unNamed
  , name

  , Refined
  , pattern Refined
  , type (?)
  , unsafeRefined
  , unRefined
  , refine
  , refinedProve1
  , refinedProve1S
  , refinedProve1S1
  , refinedProve1M
  , refinedProve1M1
  , unsafeRefinedProve1S
  , unsafeRefinedProve1S1
  , rename
  , forRefined
  , traverseRefined

  )  --}
  where

import Control.Applicative
import Control.Monad
import Data.Aeson qualified as Ae
import Data.Aeson.Types qualified as Ae
import Data.Coerce
import Data.Binary qualified as Bin
import Data.Scientific (Scientific)
import Data.Singletons
import Data.Kind (Type)
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

name :: forall a b. a -> (forall n. n @ a -> b) -> b
name a f = withNamed a f

withNamed :: forall a b. a -> (forall n. n @ a -> b) -> b
withNamed a f = f (MkNamed a)
{-# NOINLINE withNamed #-}

--------------------------------------------------------------------------------

newtype Refined (p :: kn -> kp) (a :: Type) = MkRefined a
  deriving newtype (Eq, Ord, Show, Ae.ToJSON)

type role Refined nominal representational
type a ? p = Refined p a

unsafeRefined :: forall p a. a -> a ? p
unsafeRefined = coerce
{-# INLINE unsafeRefined #-}

unRefined :: forall p a. a ? p -> a
unRefined = coerce
{-# INLINE unRefined #-}

pattern Refined :: forall p a. a -> a ? p
pattern Refined a <- (unRefined -> a)
{-# COMPLETE Refined #-}

refine :: forall p n a. n @ a -> Proof (p n) -> a ? p
refine (Named a) _ = MkRefined a
{-# INLINE refine #-}

refinedProve1 :: forall p a. Prove1 p a => a -> Maybe (a ? p)
refinedProve1 a = name a $ \na -> refine na <$> hush (prove1 na)
{-# INLINE refinedProve1 #-}

rename :: a ? p -> (forall n. n @ a -> Proof (p n) -> b) -> b
rename (Refined a) g = g (MkNamed a) axiom
{-# NOINLINE rename #-}

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

lt :: Ord x
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (LT l r))) (Proof (LT l r))
lt fa fb = \(Named la) (Named rb) ->
  if fb rb < fa la then Right axiom else Left axiom

eq :: Eq x
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (EQ l r))) (Proof (EQ l r))
eq fa fb = \(Named la) (Named rb) ->
  if fb rb == fa la then Right axiom else Left axiom

gt :: Ord x
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (GT l r))) (Proof (GT l r))
gt fa fb = \(Named la) (Named rb) ->
  if fb rb > fa la then Right axiom else Left axiom

le :: Ord x
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (LE l r))) (Proof (LE l r))
le fa fb = \l r -> either (Right . mp notGT)
                          (Left . mp gtNotLE)
                          (gt fa fb l r)

ne :: Eq x
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (NE l r))) (Proof (NE l r))
ne fa fb = \l r -> either (Right . mp notEQ)
                          (Left . mp eqNotNE)
                          (eq fa fb l r)

ge :: Ord x
   => (a -> x)
   -> (b -> x)
   -> l @ a
   -> r @ b
   -> Either (Proof (NOT (GE l r))) (Proof (GE l r))
ge fa fb = \l r -> either (Right . mp notLT)
                          (Left . mp ltNotGE)
                          (lt fa fb l r)

--------------------------------------------------------------------------------

class Prove (p :: k) where
  prove' :: Either (Proof (NOT p)) (Proof p)

prove :: forall {k} (p :: k). Prove p => Either (Proof (NOT p)) (Proof p)
prove = prove' @k @p

instance Prove p => Prove (NOT p) where
  prove' = case prove @p of
             Right _ -> Left  axiom
             Left  _ -> Right axiom

instance forall p q na. Prove (AND (p na) (q na)) => Prove (AND1 p q na) where
  prove' = case prove @(AND (p na) (q na)) of
              Right _ -> Right axiom
              Left  _ -> Left  axiom

instance forall p q. (Prove p, Prove q) => Prove (AND p q) where
  prove' = case (prove @p, prove @q) of
              (Right _, Right _) -> Right axiom
              _ -> Left axiom

instance forall p q na. Prove (OR (p na) (q na)) => Prove (OR1 p q na) where
  prove' = case prove @(OR (p na) (q na)) of
              Right _ -> Right axiom
              Left  _ -> Left  axiom

instance forall p q. (Prove p, Prove q) => Prove (OR p q) where
  prove' = case (prove @p, prove @q) of
              (Right _, _) -> Right axiom
              (_, Right _) -> Right axiom
              _            -> Left  axiom

-------------------------------------------------------------------------------

-- class Description1 (f :: Type -> Type) where
--   description1 :: ShowS
--
-- instance forall p. Description1 p => Description1 (NOT1 p) where
--   description1 = showString "not (" . description1 @p . showChar ')'
--
-- instance forall l r. (Description1 l, Description1 r) => Description1 (AND1 l r) where
--   description1 = showChar '(' . description1 @l . showString ") and ("
--                . description1 @r . showChar ')'
--
-- instance forall l r. (Description1 l, Description1 r) => Description1 (OR1 l r) where
--   description1 = showChar '(' . description1 @l . showString ") or ("
--                . description1 @r . showChar ')'
--
-- instance {-# OVERLAPPABLE #-} forall a t.
--   (NamedI a t, Show t) => Description1 (GT (a @ t)) where
--   description1 = showString "more than " . showsPrec appPrec1 (unNamedI @a @t)
--
-- instance {-# OVERLAPPABLE #-} forall z t.
--   (NamedI z t, Show t) => Description1 (LT (z @ t)) where
--   description1 = showString "less than " . showsPrec appPrec1 (unNamedI @z @t)
--
-- instance {-# OVERLAPPABLE #-} forall y t.
--   (NamedI y t, Show t) => Description1 (EQ (y @ t)) where
--   description1 = showString "equal to " . showsPrec appPrec1 (unNamedI @y @t)

--------------------------------------------------------------------------------

class Prove1 (p :: kn -> kpn) (a :: Type) where
  prove1' :: n @ a -> Either (Proof (NOT (p n))) (Proof (p n))

prove1
  :: forall {kn} {kpn} (p :: kn -> kpn) (a :: Type) (n :: kn)
  .  Prove1 p a
  => n @ a
  -> Either (Proof (NOT (p n))) (Proof (p n))
prove1 = prove1'
{-# INLINE prove1 #-}

instance Prove1 p a => Prove1 (NOT1 p) a where
  prove1' na | Left _ <- prove1 @p @a na = Right axiom
             | otherwise                 = Left  axiom

instance (Prove1 f a, Prove1 g a) => Prove1 (AND1 f g) a where
  prove1' na = case (prove1 @f @a na, prove1 @g @a na) of
    (Right fna, Right gna) -> Right (and1 $* (PDP.and $* fna $* gna))
    _ -> Left axiom


instance (Prove1 f a, Prove1 g a) => Prove1 (OR1 f g) a where
  prove1' na = case (prove1 @f @a na, prove1 @g @a na) of
    (Right _, _) -> Right axiom
    (_, Right _) -> Right axiom
    _            -> Left  axiom

instance Ord x => Prove2 LT x x where
  prove2' nz na
    | unNamed na < unNamed nz = Right axiom
    | otherwise = Left axiom

instance Ord x => Prove2 GT x x where
  prove2' na nz
    | unNamed nz > unNamed na = Right axiom
    | otherwise = Left axiom

instance Ord x => Prove2 EQ x x where
  prove2' na nb
    | unNamed nb == unNamed na = Right axiom
    | otherwise = Left axiom

instance forall ka kb kp (p :: ka -> kb -> kp) (na :: ka) (b :: Type).
  ( SingKind ka
  , SingI na
  , Prove2 p (Demote ka) b
  ) => Prove1 (p na) b where
  prove1' = prove2 (demoteNamed @na)
  {-# INLINE prove1' #-}

demoteNamed :: forall {k} (n :: k). (SingKind k, SingI n) => n @ Demote k
demoteNamed = unsafeNamed (demote @n)

class Prove2 (p :: kna -> knb -> kpnanb) (a :: Type) (b :: Type) where
  prove2' :: na @ a -> nb @ b -> Either (Proof (NOT (p na nb))) (Proof (p na nb))

prove2
  :: forall {kna} {knb} {kpnanb} (p :: kna -> knb -> kpnanb)
     (a :: Type) (b :: Type) (na :: kna) (nb :: knb)
  .  Prove2 p a b
  => na @ a
  -> nb @ b
  -> Either (Proof (NOT (p na nb))) (Proof (p na nb))
prove2 = prove2'
{-# INLINE prove2 #-}


-- #define INST_PUD(P, U, D) \
--   instance forall n. Prove1 (P n) U => Prove1 (P n) U where { \
--     prove1' = fmap (Prelude.const axiom) . prove1 @(P n); }
--
-- #define INST_ORD_UD(U, D) \
--    INST_PUD(LT, U, D); \
--    INST_PUD(EQ, U, D); \
--    INST_PUD(GT, U, D);
--
-- INST_ORD_UD(Natural    , Integer)
-- INST_ORD_UD(Natural    , Rational)
-- INST_ORD_UD(Natural    , Scientific)
-- INST_ORD_UD(Integer    , Natural)
-- INST_ORD_UD(Integer    , Rational)
-- INST_ORD_UD(Integer    , Scientific)
-- INST_ORD_UD(Rational   , Natural)
-- INST_ORD_UD(Rational   , Integer)
-- INST_ORD_UD(Rational   , Scientific)
-- INST_ORD_UD(Scientific , Natural)
-- INST_ORD_UD(Scientific , Integer)
-- INST_ORD_UD(Scientific , Rational)

--------------------------------------------------------------------------------

toJSON :: forall p a. (Ae.ToJSON a) => a ? p -> Ae.Value
toJSON = toJSON' Ae.toJSON

toJSON' :: forall p a. (a -> Ae.Value) -> a ? p -> Ae.Value
toJSON' f = f . unRefined

parseJSON
  :: forall p a
  .  Ae.FromJSON a
  => (forall n. n @ a -> Either String (Proof (p n)))
  -> Ae.Value
  -> Ae.Parser (a ? p)
parseJSON = parseJSON' Ae.parseJSON

parseJSON'
  :: forall p a
  .  (Ae.Value -> Ae.Parser a)
  -> (forall n. n @ a -> Either String (Proof (p n)))
  -> Ae.Value
  -> Ae.Parser (a ? p)
parseJSON' gma f =
  gma >=> \a ->
  name a $ \na ->
  either fail (pure . refine na) (f na)

parserJSON
  :: forall p a
  .  Ae.Parser a
  -> (forall n. n @ a -> Either String (Proof (p n)))
  -> Ae.Parser (a ? p)
parserJSON ma f = parseJSON' (\_ -> ma) f Ae.Null

--------------------------------------------------------------------------------

putBin :: forall p a. (Bin.Binary a) => a ? p -> Bin.Put
putBin = putBin' Bin.put

putBin' :: forall p a. (a -> Bin.Put) -> a ? p -> Bin.Put
putBin' f = f . unRefined

getBin
  :: forall p a
  .  (Bin.Binary a)
  => (forall n. n @ a -> Either String (Proof (p n)))
  -> Bin.Get (a ? p)
getBin = getBin' Bin.get

getBin'
  :: forall p a
  .  Bin.Get a
  -> (forall n. n @ a -> Either String (Proof (p n)))
  -> Bin.Get (a ? p)
getBin' ma f =
  ma >>= \a ->
  name a $ \(na :: n @ a) ->
  either fail (pure . refine na) (f na)

--------------------------------------------------------------------------------

hush :: Either a b -> Maybe b
hush = either (\_ -> Nothing) Just
