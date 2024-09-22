module Main (main) where

import Control.Monad.Except
import Data.Text qualified as T
import SF2TAL.A qualified as A
import SF2TAL.C qualified as C
import SF2TAL.Common
import SF2TAL.F
import SF2TAL.K qualified as K
import SF2TAL.Middle qualified as M
import SF2TAL.Tal qualified as Tal
import Test.Hspec


factorial :: Tm
factorial =
  Fix
    "f"
    "n"
    TInt
    TInt
    ( If0
        (Var "n")
        (IntLit 1)
        (Bin Mul (Var "n") (Var "f" `App` Bin Sub (Var "n") (IntLit 1)))
    )
    `App` IntLit 6


fibonacci :: Tm
fibonacci =
  Fix "f" "n" TInt TInt $
    If0 (Var "n") (IntLit 0) $
      If0 (Bin Sub (Var "n") (IntLit 1)) (IntLit 1) $
        Bin
          Add
          (Var "f" `App` Bin Sub (Var "n") (IntLit 1))
          (Var "f" `App` Bin Sub (Var "n") (IntLit 2))


twice :: Tm
twice =
  AbsT "a" $
    Fix "" "f" (TVar "a" `TFun` TVar "a") (TVar "a" `TFun` TVar "a") $
      Fix "" "x" (TVar "a") (TVar "a") $
        Var "f" `App` (Var "f" `App` Var "x")


currying :: Tm
currying =
  Fix
    ""
    "foo"
    (TInt `TFun` (TInt `TFun` TInt))
    TInt
    ( Fix
        ""
        "foo3"
        (TInt `TFun` TInt)
        TInt
        (Var "foo3" `App` IntLit 10)
        `App` (Var "foo" `App` IntLit 3)
    )
    `App` Fix
      ""
      "m"
      TInt
      (TInt `TFun` TInt)
      (Fix "" "n" TInt TInt $ Bin Add (Bin Mul (Var "m") (IntLit 2)) (Var "n"))


run :: Tm -> Either T.Text Tal.Val
run e = runExcept $ runUniqT $ do
  e' <- liftEither $ ty e
  k <- K.kProg e'
  liftEither $ withError ("K: " <>) $ M.ckTm k

  c <- C.cProg k
  liftEither $ withError ("C: " <>) $ M.ckProg c

  a <- A.aProg c
  liftEither $ withError ("A: " <>) $ M.ckProg a

  (tal, ths) <- Tal.tProg a
  liftEither $ withError ("T: " <>) $ Tal.ckProg ths tal
  Tal.exec ths tal


main :: IO ()
main = hspec $ do
  it "factorial" $ run factorial `shouldBe` Right (Tal.IntLit 720)
  it "fibonacci" $
    run (fibonacci `App` IntLit 10) `shouldBe` Right (Tal.IntLit 55)
  it "twice fibbonacci" $
    run (((twice `AppT` TInt) `App` fibonacci) `App` IntLit 7)
      `shouldBe` Right (Tal.IntLit 233)
  it "currying" $ run currying `shouldBe` Right (Tal.IntLit 16)
