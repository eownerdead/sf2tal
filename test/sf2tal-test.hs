module Main (main) where

import SF2TAL
import SF2TAL.F
import SF2TAL.Tal qualified as Tal
import Test.Hspec


{- FOURMOLU_DISABLE -}
factorial :: Tm
factorial =
  Fix "f" "n" TInt TInt
    ( If0 (Var "n")
        (IntLit 1)
        (Var "n" #* (Var "f" #$ (Var "n" #- IntLit 1)))
    )
    #$ IntLit 6
{- FOURMOLU_ENABLE -}


fibonacci :: Tm
fibonacci =
  Fix "f" "n" TInt TInt $
    If0 (Var "n") (IntLit 0) $
      If0 (Var "n" #- IntLit 1) (IntLit 1) $
        (Var "f" #$ (Var "n" #- IntLit 1)) #+ (Var "f" #$ (Var "n" #- IntLit 2))


twice :: Tm
twice =
  AbsT "a" $
    Fix "" "f" (TVar "a" #-> TVar "a") (TVar "a" #-> TVar "a") $
      Fix "" "x" (TVar "a") (TVar "a") $
        Var "f" #$ (Var "f" #$ Var "x")

{- FOURMOLU_DISABLE -}
currying :: Tm
currying =
  Fix "" "foo" (TInt #-> TInt #-> TInt) TInt
    ( Fix "" "foo3" (TInt #-> TInt) TInt (Var "foo3" #$ IntLit 10)
        #$ (Var "foo" #$ IntLit 3)
    )
    #$ Fix "" "m" TInt (TInt #-> TInt)
      (Fix "" "n" TInt TInt $ (Var "m" #* IntLit 2) #+ Var "n")
{- FOURMOLU_ENABLE -}


main :: IO ()
main = hspec $ do
  it "factorial" $ run factorial `shouldBe` Tal.IntLit 720
  it "fibonacci" $
    run (fibonacci #$ IntLit 10) `shouldBe` Tal.IntLit 55
  it "twice fibbonacci" $
    run (twice `AppT` TInt #$ fibonacci #$ IntLit 7)
      `shouldBe` Tal.IntLit 233
  it "currying" $ run currying `shouldBe` Tal.IntLit 16
