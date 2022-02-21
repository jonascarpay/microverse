{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Control.Monad
import Data.Typeable
import Test.HUnit
import Test.Hspec
import Universe

fnShouldMatch :: (Eq b, Show a, Show b) => (a -> b) -> (a -> b) -> a -> Expectation
fnShouldMatch f1 f2 a = assertBool (unlines ["a:  " <> show a, "b1: " <> show b1, "b2: " <> show b2]) (b1 == b2)
  where
    b1 = f1 a
    b2 = f2 a

forType :: forall a. (Show a, Typeable a, Universe a) => Proxy a -> Spec
forType p = describe (show (typeRep p)) $ do
  it "length universe is cardinality" $ length (universe :: [a]) `shouldBe` cardinality (Proxy @a)
  it "toOrdinal . next is next . toOrdinal" $ forM_ (universe :: [a]) $ fnShouldMatch (next . toOrdinal) (fmap toOrdinal . next)
  it "toOrdinal . prev is prev . toOrdinal" $ forM_ (universe :: [a]) $ fnShouldMatch (prev . toOrdinal) (fmap toOrdinal . prev)
  it "toOrdinal <$> universe is universe" $ toOrdinal <$> (universe :: [a]) `shouldBe` universe
  it "fromOrdinal <$> universe is universe" $ fromOrdinal <$> (universe :: [Ordinal a]) `shouldBe` universe
  it "universe is in ascending order" $
    forM_ (zip universe (tail universe)) $ \(lo :: a, hi :: a) ->
      assertBool (show lo <> " >= " <> show hi) (lo < hi)
  it "next . prev is identity" $ forM_ (universe :: [a]) $ \x -> forM_ (prev x) (\x' -> next x' @?= Just x)
  it "prev . next is identity" $ forM_ (universe :: [a]) $ \x -> forM_ (next x) (\x' -> prev x' @?= Just x)
  it "only least has no prev" $ forM_ (universe :: [a]) $ \x -> assertEqual ("Failure at " <> show x) (x == least) (prev x == Nothing)
  it "only greatest has no next" $ forM_ (universe :: [a]) $ \x -> assertEqual ("Failure at " <> show x) (x == greatest) (next x == Nothing)
  it "universe bigrams are next/prev pairs" $
    forM_ (zip universe (tail universe)) $ \(lo :: a, hi :: a) -> do
      next lo @?= Just hi
      prev hi @?= Just lo

main :: IO ()
main = hspec $ do
  forType (Proxy @())
  forType (Proxy @Bool)
  forType (Proxy @(Maybe ()))
  forType (Proxy @(Maybe Bool))
  forType (Proxy @(Either () Bool))
  forType (Proxy @(Either Bool Bool))
  forType (Proxy @(Bool, Bool))
  forType (Proxy @(Bool, Maybe Bool))
  forType (Proxy @(Ordinal (Bool, Maybe Bool)))
  forType (Proxy @((Bool, Maybe (Either (Maybe ()) ())), Maybe (Bool, Either () Bool)))
