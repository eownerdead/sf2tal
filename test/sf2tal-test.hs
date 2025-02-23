module Main (main) where

import Data.Map qualified as Map
import SF2TAL
import SF2TAL.F
import SF2TAL.Tal qualified as Tal
import Test.Hspec


{- FOURMOLU_DISABLE -}
factorial :: Tm
factorial =
  LetRec (Map.fromList
    [("f", (TInt #-> TInt,
      Abs "n" TInt TInt do
        If0 (Var "n")
          do IntLit 1
          do Var "n" #* (Var "f" #$ (Var "n" #- IntLit 1))
    ))]
  )
    do Var "f" #$ IntLit 6


fibonacci :: Tm
fibonacci =
  LetRec (Map.fromList
    [( "f", ( TInt #-> TInt,
      Abs "n" TInt TInt do
        If0 (Var "n") (IntLit 0) $
          If0 (Var "n" #- IntLit 1) (IntLit 1) $
            (Var "f" #$ (Var "n" #- IntLit 1))
              #+ (Var "f" #$ (Var "n" #- IntLit 2))
    ))]
  )
    do Var "f"
{- FOURMOLU_ENABLE -}


twice :: Tm
twice =
  AbsT "a" $
    Abs "f" (TVar "a" #-> TVar "a") (TVar "a" #-> TVar "a") $
      Abs "x" (TVar "a") (TVar "a") do
        Var "f" #$ (Var "f" #$ Var "x")

{- FOURMOLU_DISABLE -}
currying :: Tm
currying =
  Abs "foo" (TInt #-> TInt #-> TInt) TInt
    ( Abs "foo3" (TInt #-> TInt) TInt (Var "foo3" #$ IntLit 10)
        #$ (Var "foo" #$ IntLit 3)
    )
    #$ Abs "m" TInt (TInt #-> TInt)
      (Abs "n" TInt TInt $ (Var "m" #* IntLit 2) #+ Var "n")
{- FOURMOLU_ENABLE -}


main :: IO ()
main = hspec $ do
  it "factorial" $ run factorial `shouldBe` Tal.IntLit 720
  it "fibonacci" $
    run (fibonacci #$ IntLit 10) `shouldBe` Tal.IntLit 55
  it "twice fibbonacci" $
    run (((twice `AppT` TInt) #$ fibonacci) #$ IntLit 7)
      `shouldBe` Tal.IntLit 233
  it "currying" $ run currying `shouldBe` Tal.IntLit 16
