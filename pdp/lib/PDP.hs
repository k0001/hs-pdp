{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

#include "MachDeps.h"

module PDP {--}
   ( -- * Types
    TRUE
   , FALSE
   , AND
   , AND1
   , OR
   , OR1
   , NOT
   , NOT1
   , XOR
   , XNOR
   , type (-->)

    -- * Proofs
   , Proof (..)
   , true
   , mp
   , mt
   , trans
   , swapAND
   , swapAND1
   , swapOR
   , swapOR1
   , inOR1
   , unOR1
   , inAND1
   , unAND1
   , dmAND
   , dmAND1
   , dmOR
   , dmOR1
   , curryAND
   , uncurryAND
   , curryOR
   , uncurryOR
   , inlOR
   , inrOR
   , lmapOR
   , rmapOR
   , inAND
   , lmapAND
   , rmapAND
   , fstAND
   , sndAND
   , exfalso
   , inNOT1
   , unNOT1
   , LT
   , LE
   , EQ
   , GE
   , GT
   , NE
   , Cmp (..)
   , cmp
   , asymGT
   , asymLT
   , eqNotNE
   , geLE
   , gtLT
   , gtNE
   , gtNotLE
   , leGE
   , ltGT
   , ltNE
   , ltNotGE
   , notEQ
   , notGE
   , notGT
   , notLE
   , notLT
   , reflEQ
   , symEQ
   , symNE
   , transEQ
   , transGE
   , transGT
   , transLE
   , transLT

    -- * Named
   , Name (Name)
   , Named
   , pattern Named
   , type (@)
   , unsafeNamed
   , unsafeMapNamed
   , unNamed
   , named

    -- * Refined
   , Refined
   , pattern Refined
   , type (?)
   , unRefined
   , unsafeRefined
   ) -- }
where

import Control.Arrow ((&&&))
import Data.Coerce
import Data.Kind (Type)

--------------------------------------------------------------------------------

data Proof (p :: Type)
   = -- | Be careful with this constructor! Mostly just use it to define axioms.
     QED
   deriving (Eq, Ord, Show)

type a --> b = NOT a `OR` b
type (-->) :: Type -> Type -> Type
infixr 0 -->

data TRUE

type FALSE = NOT TRUE

data AND l r
type AND :: Type -> Type -> Type
infixl 7 `AND`

data AND1 f g x
type AND1 :: (Type -> Type) -> (Type -> Type) -> Type -> Type
infixl 7 `AND1`

data OR l r
type OR :: Type -> Type -> Type
infixl 5 `OR`

data OR1 f g x
type OR1 :: (Type -> Type) -> (Type -> Type) -> Type -> Type
infixl 5 `OR1`

data NOT a
type NOT :: Type -> Type

data NOT1 f x
type NOT1 :: (Type -> Type) -> Type -> Type

type XOR l r = (l `AND` NOT r) `OR` (NOT l `AND` r)
type XOR :: Type -> Type -> Type
infixl 4 `XOR`

type XNOR l r = (l `AND` r) `OR` NOT (l `OR` r)
type XNOR :: Type -> Type -> Type
infixl 4 `XNOR`

true :: Proof TRUE
true = QED

-- | Modus ponens.
mp :: Proof (a -> b) -> Proof a -> Proof b
mp _ _ = QED

trans :: (Proof b -> Proof c) -> (Proof a -> Proof b) -> (Proof a -> Proof c)
trans _ _ _ = QED

swapAND :: Proof (AND l r) -> Proof (AND r l)
swapAND _ = QED

swapAND1 :: Proof (AND1 f g x) -> Proof (AND1 g f x)
swapAND1 _ = QED

swapOR :: Proof (OR l r) -> Proof (OR r l)
swapOR _ = QED

swapOR1 :: Proof (OR1 f g x) -> Proof (OR1 g f x)
swapOR1 _ = QED

inOR1 :: Proof (OR (f x) (g x)) -> Proof (OR1 f g x)
inOR1 _ = QED

unOR1 :: Proof (OR1 f g x) -> Proof (OR (f x) (g x))
unOR1 _ = QED

inAND1 :: Proof (AND (f x) (g x)) -> Proof (AND1 f g x)
inAND1 _ = QED

unAND1 :: Proof (AND1 f g x) -> Proof (AND (f x) (g x))
unAND1 _ = QED

-- | De morgan.
dmAND :: Proof (OR (NOT l) (NOT r)) -> Proof (NOT (AND p q))
dmAND _ = QED

-- | De morgan.
dmAND1 :: Proof (OR1 (NOT1 f) (NOT1 g) x) -> Proof (NOT1 (AND1 f g) x)
dmAND1 _ = QED

-- | De morgan.
dmOR :: Proof (AND (NOT l) (NOT r)) -> Proof (NOT (OR p q))
dmOR _ = QED

-- | De morgan.
dmOR1 :: Proof (AND1 (NOT1 f) (NOT1 g) x) -> Proof (NOT1 (OR1 f g) x)
dmOR1 _ = QED

-- | Modus Tollens.
mt :: (Proof a -> Proof b) -> Proof (NOT b) -> Proof (NOT a)
mt _ _ = QED

curryAND :: (Proof (AND a b) -> Proof c) -> Proof a -> Proof b -> Proof c
curryAND _ _ _ = QED

uncurryAND :: (Proof a -> Proof b -> Proof c) -> Proof (AND a b) -> Proof c
uncurryAND _ _ = QED

curryOR :: (Proof (OR a b) -> Proof c) -> Either (Proof a) (Proof b) -> Proof c
curryOR _ _ = QED

uncurryOR :: (Either (Proof a) (Proof b) -> Proof c) -> Proof (OR a b) -> Proof c
uncurryOR _ _ = QED

inlOR :: Proof a -> Proof (OR a b)
inlOR _ = QED

inrOR :: Proof b -> Proof (OR a b)
inrOR _ = QED

lmapOR :: (Proof a -> Proof a') -> Proof (OR a b) -> Proof (OR a' b)
lmapOR _ _ = QED

rmapOR :: (Proof b -> Proof b') -> Proof (OR a b) -> Proof (OR a b')
rmapOR _ _ = QED

inAND :: Proof a -> Proof b -> Proof (AND a b)
inAND _ _ = QED

lmapAND :: (Proof a -> Proof a') -> Proof (AND a b) -> Proof (AND a' b)
lmapAND _ _ = QED

rmapAND :: (Proof b -> Proof b') -> Proof (AND a b) -> Proof (AND a b')
rmapAND _ _ = QED

fstAND :: Proof (AND a b) -> Proof a
fstAND _ = QED

sndAND :: Proof (AND a b) -> Proof b
sndAND _ = QED

exfalso :: Proof FALSE -> Proof a
exfalso _ = QED

inNOT1 :: Proof (NOT (f x)) -> Proof (NOT1 f x)
inNOT1 _ = QED

unNOT1 :: Proof (NOT1 f x) -> Proof (NOT (f x))
unNOT1 _ = QED

--------------------------------------------------------------------------------

type Named :: Type -> Type -> Type
newtype Named n a = UnsafeNamed a
   deriving newtype (Eq, Ord, Show)

type role Named nominal representational
type (@) = Named

-- | To define a new name, create a @newtype@ around 'Name' and use
-- 'unsafeNamed'. Do not export the @newtype@ constructor.
data Name = Name

unsafeNamed :: forall n a. (Coercible Name n, Coercible n Name) => a -> n @ a
unsafeNamed = coerce
{-# INLINE unsafeNamed #-}

unNamed :: forall n a. n @ a -> a
unNamed = coerce
{-# INLINE unNamed #-}

pattern Named :: forall n a. a -> n @ a
pattern Named a <- (coerce -> a)
{-# COMPLETE Named #-}

named :: forall a b. a -> (forall (n :: Type). n @ a -> b) -> b
named a f = f (coerce a)
{-# INLINE named #-}

unsafeMapNamed :: forall a b n. (a -> b) -> n @ a -> n @ b
unsafeMapNamed = coerce
{-# INLINE unsafeMapNamed #-}

--------------------------------------------------------------------------------

type role Refined nominal representational

type Refined :: (Type -> Type) -> Type -> Type
newtype Refined p a = UnsafeRefined a
   deriving newtype (Eq, Ord, Show)

type a ? p = Refined p a

unsafeRefined :: forall p a. a -> a ? p
unsafeRefined = coerce
{-# INLINE unsafeRefined #-}

unRefined :: forall p a. a ? p -> a
unRefined = coerce
{-# INLINE unRefined #-}

pattern Refined :: forall p n a. n @ a -> Proof (p n) -> a ? p
pattern Refined na pn <- (coerce &&& const QED -> (na, pn))
   where
      Refined na _ = coerce na
{-# COMPLETE Refined #-}

--------------------------------------------------------------------------------

-- | @x < y@, according to 'Ord'.
data LT y x

type LT :: Type -> Type -> Type

-- | @x == y@, according to 'Ord'.
data EQ y x

type EQ :: Type -> Type -> Type

-- | @x > y@, according to 'Ord'.
data GT y x

type GT :: Type -> Type -> Type

-- | @x /= y@, according to 'Ord'.
type NE y = OR1 (LT y) (GT y)

type NE :: Type -> Type -> Type

-- | @x <= y@, according to 'Ord'.
type LE y = OR1 (LT y) (EQ y)

type LE :: Type -> Type -> Type

-- | @x >= y@, according to 'Ord'.
type GE y = OR1 (GT y) (EQ y)

type GE :: Type -> Type -> Type

transLT :: Proof (LT a b) -> Proof (LT b c) -> Proof (LT a c)
transLT _ _ = QED

asymLT :: Proof (LT a b) -> Proof (NOT (LT b a))
asymLT _ = QED

ltGT :: Proof (LT a b) -> Proof (GT b a)
ltGT _ = QED

notLT :: Proof (NOT (LT a b)) -> Proof (GE a b)
notLT _ = QED

transEQ :: Proof (EQ a b) -> Proof (EQ b c) -> Proof (EQ a c)
transEQ _ _ = QED

eqNotNE :: Proof (EQ a b) -> Proof (NOT (NE a b))
eqNotNE _ = QED

symEQ :: Proof (EQ a b) -> Proof (EQ b a)
symEQ _ = QED

reflEQ :: Proof (EQ a a)
reflEQ = QED

notEQ :: Proof (NOT (EQ a b)) -> Proof (NE a b)
notEQ _ = QED

ltNE :: Proof (LT a b) -> Proof (NE a b)
ltNE _ = QED

ltNotGE :: Proof (LT a b) -> Proof (NOT (GE a b))
ltNotGE _ = QED

gtNE :: Proof (GT a b) -> Proof (NE a b)
gtNE _ = QED

transGT :: Proof (GT a b) -> Proof (GT b c) -> Proof (GT a c)
transGT _ _ = QED

asymGT :: Proof (GT a b) -> Proof (NOT (GT b a))
asymGT _ = QED

gtLT :: Proof (GT a b) -> Proof (LT b a)
gtLT _ = QED

gtNotLE :: Proof (GT a b) -> Proof (NOT (LE a b))
gtNotLE _ = QED

notGT :: Proof (NOT (GT a b)) -> Proof (LE a b)
notGT _ = QED

transLE :: Proof (LE a b) -> Proof (LE b c) -> Proof (LE a c)
transLE _ _ = QED

leGE :: Proof (LE a b) -> Proof (GE b a)
leGE _ = QED

notLE :: Proof (NOT (LE a b)) -> Proof (GT a b)
notLE _ = QED

transGE :: Proof (GE a b) -> Proof (GE b c) -> Proof (GE a c)
transGE _ _ = QED

geLE :: Proof (GE a b) -> Proof (LE b a)
geLE _ = QED

notGE :: Proof (NOT (GE a b)) -> Proof (LT a b)
notGE _ = QED

symNE :: Proof (NE a b) -> Proof (NE b a)
symNE _ = QED

data Cmp (l :: Type) (r :: Type)
   = CmpLT (Proof (LT r l))
   | CmpEQ (Proof (EQ r l))
   | CmpGT (Proof (GT r l))
   deriving (Eq, Ord, Show)

cmp :: (Ord w) => (a -> w) -> (b -> w) -> l @ a -> r @ b -> Cmp l r
cmp fa fb (Named la) (Named rb) =
   case compare (fb rb) (fa la) of
      LT -> CmpLT QED
      EQ -> CmpEQ QED
      GT -> CmpGT QED

{-
lt :: (Ord w) => (a -> w) -> (b -> w) -> l @ a -> r @ b -> Decision (LT l r)
lt fa fb (Named la) (Named rb) =
   if fb rb < fa la then Right QED else Left QED
{-# INLINE lt #-}

eq :: (Eq w) => (a -> w) -> (b -> w) -> l @ a -> r @ b -> Decision (EQ l r)
eq fa fb (Named la) (Named rb) =
   if fb rb == fa la then Right QED else Left QED
{-# INLINE eq #-}

gt :: (Ord w) => (a -> w) -> (b -> w) -> l @ a -> r @ b -> Decision (GT l r)
gt fa fb (Named la) (Named rb) =
   if fb rb > fa la then Right QED else Left QED
{-# INLINE gt #-}

le :: (Ord w) => (a -> w) -> (b -> w) -> l @ a -> r @ b -> Decision (LE l r)
le fa fb (Named la) (Named rb) =
   if fb rb <= fa la then Right QED else Left QED
{-# INLINE le #-}

ne :: (Eq w) => (a -> w) -> (b -> w) -> l @ a -> r @ b -> Decision (NE l r)
ne fa fb (Named la) (Named rb) =
   if fb rb /= fa la then Right QED else Left QED
{-# INLINE ne #-}

ge :: (Ord w) => (a -> w) -> (b -> w) -> l @ a -> r @ b -> Decision (GE l r)
ge fa fb (Named la) (Named rb) =
   if fb rb >= fa la then Right QED else Left QED
{-# INLINE ge #-}
-}
