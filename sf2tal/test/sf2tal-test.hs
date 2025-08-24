module Main (main) where

import Data.Text.IO qualified as T
import Effectful
import SF2TAL hiding (main)
import SF2TAL.Utils
import Test.Hspec


runTest :: String -> IO Int
runTest name = do
  s <- T.readFile ("test/" <> name <> ".txt")
  runEff $ runLogStderr (const True) $ run s


runExpect :: String -> Int -> SpecWith (Arg Expectation)
runExpect name v = it name do runTest name >>= (`shouldBe` v)


main :: IO ()
main = hspec $ do
  runExpect "factorial" 720
  runExpect "fibonacci" 55
  runExpect "currying" 16
  runExpect "evenOdd" 4
  runExpect "ackermann" 8189
