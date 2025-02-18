module Main (main) where

import Data.Text qualified as T
import Effectful
import Effectful.Error.Static
import SF2TAL.F
import SF2TAL.Middle qualified as M
import SF2TAL.Middle.Opt qualified as M
import SF2TAL.Tal qualified as Tal
import SF2TAL.Uniq
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


iter :: (Uniq :> es, Error T.Text :> es) => Int -> M.Tm -> Eff es M.Tm
iter n k
  | n == 0 = pure k
  | otherwise = do
      k' <- M.simp k
      M.ckTm k'
      iter (n - 1) k'


run :: Tm -> Either T.Text Tal.Val
run e = runPureEff $ runUniq $ runErrorNoCallStack do
  e' <- ty e
  k <- M.kProg e'
  M.ckTm k

  k' <- iter 25 k

  c <- M.cProg k'
  M.ckProg c

  a <- M.aProg c
  M.ckProg a

  (tal, ths) <- Tal.tProg a
  Tal.ckProg ths tal
  Tal.exec ths tal


main :: IO ()
main = hspec $ do
  it "factorial" $ run factorial `shouldBe` Right (Tal.IntLit 720)
  it "fibonacci" $
    run (fibonacci #$ IntLit 10) `shouldBe` Right (Tal.IntLit 55)
  it "twice fibbonacci" $
    run (twice `AppT` TInt #$ fibonacci #$ IntLit 7)
      `shouldBe` Right (Tal.IntLit 233)
  it "currying" $ run currying `shouldBe` Right (Tal.IntLit 16)
