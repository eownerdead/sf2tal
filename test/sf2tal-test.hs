module Main (main) where

import Data.Text.IO qualified as T
import Effectful
import SF2TAL hiding (main)
import SF2TAL.Tal qualified as Tal
import Test.Hspec


runTest :: String -> IO Tal.Val
runTest name = do
  s <- T.readFile ("test/" <> name <> ".txt")
  runEff $ run s


runExpect :: String -> Tal.Val -> SpecWith (Arg Expectation)
runExpect name v = it name do runTest name >>= (`shouldBe` v)


main :: IO ()
main = hspec $ do
  runExpect "factorial" $ Tal.IntLit 720
  runExpect "fibonacci" $ Tal.IntLit 55
  runExpect "currying" $ Tal.IntLit 16
