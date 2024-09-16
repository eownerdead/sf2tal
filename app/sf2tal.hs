module Main where

import Control.Monad.Except
import Control.Monad.IO.Class
import Data.Text.IO qualified as T
import Prettyprinter
import Prettyprinter.Render.Text (putDoc)
import SF2TAL.A qualified as A
import SF2TAL.C qualified as C
import SF2TAL.Common
import SF2TAL.F
import SF2TAL.H qualified as H
import SF2TAL.K qualified as K
import SF2TAL.Middle qualified as M
import SF2TAL.Tal qualified as Tal


factorial :: Tm
factorial =
  App
    ( Fix "f" "n" TInt TInt $
        If0
          (Var "n")
          (IntLit 1)
          (Bin Mul (Var "n") (Var "f" `App` Bin Sub (Var "n") (IntLit 1)))
    )
    (IntLit 6)


twice :: Tm
twice =
  AbsT "a" $
    Fix "" "f" (TVar "a" `TFun` TVar "a") (TVar "a" `TFun` TVar "a") $
      Fix "" "x" (TVar "a") (TVar "a") $
        Var "f" `App` (Var "f" `App` Var "x")


main :: IO ()
main =
  runExceptT
    ( runUniqT $ do
        e <- liftEither $ ty factorial
        k <- K.kProg e
        liftIO $ T.putStrLn "K"
        liftIO $ putDoc $ pretty k
        liftEither $ M.ckTm k

        c <- C.cProg k
        liftIO $ T.putStrLn "\nC"
        liftIO $ putDoc $ pretty c
        liftEither $ M.ckTm c

        h <- H.hProg c
        liftIO $ T.putStrLn "\nH"
        liftIO $ putDoc $ pretty h
        liftEither $ M.ckProg h

        a <- A.aProg h
        liftIO $ T.putStrLn "\nA"
        liftIO $ putDoc $ pretty a
        liftEither $ M.ckProg a

        (tal, ths) <- Tal.tProg a
        liftIO $ T.putStrLn "\nTal"
        liftIO $ putDoc $ Tal.prettyMap colon ths
        liftIO $ putDoc $ pretty tal
        liftEither $ Tal.ckProg ths tal
        tal' <- Tal.exec ths tal
        liftIO $ T.putStrLn "\nExec"
        liftIO $ putDoc $ pretty tal'
        pure ()
    )
    >>= \case
      Right () -> pure ()
      Left e -> T.putStrLn $ "\nerror: " <> e
