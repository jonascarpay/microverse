{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Universe where

import Control.Applicative
import Data.Proxy
import GHC.Generics

newtype Ordinal a = UnsafeOrdinal {unOrdinal :: Int}
  deriving (Eq, Show, Ord)

toInt :: Universe a => a -> Int
toInt = unOrdinal . toOrdinal

ordinal :: forall a. Universe a => Int -> Maybe (Ordinal a)
ordinal n
  | n >= 0 && n < cardinality (Proxy :: Proxy a) = Just $ UnsafeOrdinal n
  | otherwise = Nothing

fromInt :: Universe a => Int -> Maybe a
fromInt = fmap fromOrdinal . ordinal

-- TODO INLINEs

-- A inhabited, well-ordered, bounded set
-- Formally, a type that's
--   - ordered
--   - bounded
--   - well-ordered and countable
--     - i.e. elements have indices, and an element has a distinct next and previous element
-- This means we can list all elements, from smallest to largest.
-- Well-orderedness forces it to be inhabited as well.
-- Additionally, we assume the cardinality to be reasonably small, so that we can feasibly iterate over every element
class Ord a => Universe a where
  universe :: [a]
  cardinality :: Proxy a -> Int
  toOrdinal :: a -> Ordinal a
  fromOrdinal :: Ordinal a -> a
  least :: a
  greatest :: a
  next :: a -> Maybe a
  prev :: a -> Maybe a

  default universe :: (Generic a, GUniverse (Rep a)) => [a]
  universe = to <$> guniverse

  default cardinality :: (GUniverse (Rep a)) => Proxy a -> Int
  cardinality _ = gcardinality (Proxy :: Proxy (Rep a x))

  default toOrdinal :: (Generic a, GUniverse (Rep a)) => a -> Ordinal a
  toOrdinal = UnsafeOrdinal . gtoOrdinal . from

  default fromOrdinal :: (Generic a, GUniverse (Rep a)) => Ordinal a -> a
  fromOrdinal = to . gfromOrdinal . unOrdinal

  default least :: (Generic a, GUniverse (Rep a)) => a
  least = to gleast

  default greatest :: (Generic a, GUniverse (Rep a)) => a
  greatest = to ggreatest

  default next :: (Generic a, GUniverse (Rep a)) => a -> Maybe a
  next = fmap to . gnext . from

  default prev :: (Generic a, GUniverse (Rep a)) => a -> Maybe a
  prev = fmap to . gprev . from

instance Universe a => Universe (Ordinal a) where
  universe = UnsafeOrdinal <$> take (cardinality (Proxy @a)) [0 ..]
  cardinality _ = cardinality (Proxy @a)
  toOrdinal = UnsafeOrdinal . unOrdinal
  fromOrdinal = UnsafeOrdinal . unOrdinal
  least = UnsafeOrdinal 0
  greatest = UnsafeOrdinal (cardinality (Proxy @a) - 1)
  next (UnsafeOrdinal n) = let n' = n + 1 in if n' < cardinality (Proxy @a) then Just (UnsafeOrdinal n') else Nothing
  prev (UnsafeOrdinal n) = if n <= 0 then Nothing else Just (UnsafeOrdinal (n - 1))

class GUniverse a where
  guniverse :: [a x]
  gcardinality :: Proxy (a x) -> Int
  gtoOrdinal :: a x -> Int
  gfromOrdinal :: Int -> a x
  gleast :: a x
  ggreatest :: a x
  gnext :: a x -> Maybe (a x)
  gprev :: a x -> Maybe (a x)

instance Universe ()

instance Universe Bool

instance Universe a => Universe (Maybe a)

instance (Universe a, Universe b) => Universe (Either a b)

instance (Universe a, Universe b) => Universe (a, b)

instance (Universe a, Universe b, Universe c) => Universe (a, b, c)

instance GUniverse U1 where
  guniverse = pure U1
  gcardinality _ = 1
  gtoOrdinal _ = 0
  gfromOrdinal _ = U1
  gleast = U1
  ggreatest = U1
  gnext _ = Nothing
  gprev _ = Nothing

instance Universe a => GUniverse (K1 i a) where
  guniverse = K1 <$> universe
  gcardinality _ = cardinality (Proxy :: Proxy a)
  gtoOrdinal = unOrdinal . toOrdinal . unK1
  gfromOrdinal = K1 . fromOrdinal . UnsafeOrdinal
  gleast = K1 least
  ggreatest = K1 greatest
  gnext = fmap K1 . next . unK1
  gprev = fmap K1 . prev . unK1

instance GUniverse f => GUniverse (M1 i c f) where
  guniverse = M1 <$> guniverse
  gcardinality _ = gcardinality (Proxy :: Proxy (f x))
  gtoOrdinal = gtoOrdinal . unM1
  gfromOrdinal = M1 . gfromOrdinal
  gleast = M1 gleast
  ggreatest = M1 ggreatest
  gnext = fmap M1 . gnext . unM1
  gprev = fmap M1 . gprev . unM1

instance (GUniverse l, GUniverse r) => GUniverse ((:*:) l r) where
  guniverse = liftA2 (:*:) guniverse guniverse
  gcardinality _ = gcardinality (Proxy :: Proxy (l x)) * gcardinality (Proxy :: Proxy (r x))
  gtoOrdinal =
    let !nr = gcardinality (Proxy :: Proxy (r x))
     in \(l :*: r) -> gtoOrdinal l * nr + gtoOrdinal r
  gfromOrdinal =
    let !nr = gcardinality (Proxy :: Proxy (r x))
     in \ix -> let (il, ir) = divMod ix nr in (gfromOrdinal il :*: gfromOrdinal ir)
  gleast = gleast :*: gleast
  ggreatest = ggreatest :*: ggreatest
  gnext (l :*: r) = (l :*:) <$> gnext r <|> (:*: gleast) <$> gnext l
  gprev (l :*: r) = (l :*:) <$> gprev r <|> (:*: ggreatest) <$> gprev l

instance (GUniverse l, GUniverse r) => GUniverse ((:+:) l r) where
  guniverse = (L1 <$> guniverse) <> (R1 <$> guniverse)
  gcardinality _ = gcardinality (Proxy :: Proxy (l x)) + gcardinality (Proxy :: Proxy (r x))
  gtoOrdinal =
    let !nl = gcardinality (Proxy :: Proxy (l x))
     in \case
          L1 l -> gtoOrdinal l
          R1 r -> gtoOrdinal r + nl
  gfromOrdinal =
    let !nl = gcardinality (Proxy :: Proxy (l x))
     in \ix -> if ix < nl then L1 (gfromOrdinal ix) else R1 (gfromOrdinal (ix - nl))
  gleast = L1 gleast
  ggreatest = R1 ggreatest
  gnext (L1 l) = Just $ maybe (R1 gleast) L1 (gnext l)
  gnext (R1 r) = R1 <$> gnext r

  gprev (L1 l) = L1 <$> gprev l
  gprev (R1 r) = Just $ maybe (L1 ggreatest) R1 (gprev r)
