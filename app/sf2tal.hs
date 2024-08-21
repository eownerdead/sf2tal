module Main where

import Control.Monad.Except
import Control.Monad.IO.Class
import Data.Text.IO qualified as T
import Prettyprinter
import Prettyprinter.Render.Text (putDoc)
import SF2TAL
import SF2TAL.Common


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
        k <- kProg e
        liftIO $ T.putStrLn "K"
        liftIO $ putDoc $ pretty k
        liftEither $ ckTm k

        c <- cProg k
        liftIO $ T.putStrLn "\nC"
        liftIO $ putDoc $ pretty c
        liftEither $ ckTm c

        h <- hProg c
        liftIO $ T.putStrLn "\nH"
        liftIO $ putDoc $ pretty h
        liftEither $ ckProg h

        !a <- aProg h
        liftIO $ T.putStrLn "\nA"
        liftIO $ putDoc $ pretty a
        liftEither $ ckProg a
        pure ()
    )
    >>= \case
      Right () -> pure ()
      Left e -> T.putStrLn $ "\nerror: " <> e
