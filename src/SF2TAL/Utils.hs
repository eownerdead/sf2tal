module SF2TAL.Utils
  ( classIdFields
  , makeFieldsId
  , int2Text
  , universeOf
  , universeOnOf
  , MonadUniq (..)
  , UniqT
  , Uniq
  , runUniqT
  , runUniq
  , brackets
  , parens
  , angles
  , braces
  , prettyText
  )
where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Data.Char
import Data.Coerce
import Data.Functor.Identity
import Data.Monoid
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
import Data.Text.Lazy.Builder qualified as LT
import Data.Text.Lazy.Builder.Int qualified as LT
import Language.Haskell.TH qualified as TH
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text qualified as PP


int2Text :: Int -> T.Text
int2Text = LT.toStrict . LT.toLazyText . LT.decimal


makeFieldsId :: TH.Name -> TH.DecsQ
makeFieldsId = makeLensesWith classIdFields


classIdFields :: LensRules
classIdFields =
  lensRules
    & createClass
    .~ True
    & lensField
    .~ \_ _ n -> case TH.nameBase n of
      x : xs ->
        [ MethodName
            (TH.mkName $ "Has" <> (toUpper x : xs))
            (TH.mkName $ x : xs)
        ]
      _ -> []


universeOf :: Getting (Endo [a]) a a -> a -> [a]
universeOf l x = appEndo (universeOf' l x) []


universeOf' :: Getting (Endo [a]) a a -> a -> Endo [a]
universeOf' l = go
  where
    go a = Endo (a :) <> coerce l go a


universeOnOf :: Getting (Endo [a]) s a -> Getting (Endo [a]) a a -> s -> [a]
universeOnOf b p x = appEndo (coerce b (universeOf' p) x) []


class Monad m => MonadUniq m where
  fresh :: m Int


type UniqT = StateT Int


type Uniq = UniqT Identity


instance {-# OVERLAPS #-} Monad m => MonadUniq (UniqT m) where
  fresh = state $ \n -> (n, n + 1)


instance MonadUniq m => MonadUniq (ExceptT e m) where
  fresh = lift fresh


instance (Monoid w, MonadUniq m) => MonadUniq (RWST r w s m) where
  fresh = lift fresh


instance MonadUniq m => MonadUniq (StateT s m) where
  fresh = lift fresh


instance (Monoid w, MonadUniq m) => MonadUniq (WriterT w m) where
  fresh = lift fresh


runUniqT :: Monad m => UniqT m a -> m a
runUniqT m = evalStateT m 0


runUniq :: Uniq a -> a
runUniq m = evalState m 0


brackets' :: PP.Doc a -> PP.Doc a -> PP.Doc a -> [PP.Doc a] -> PP.Doc a
brackets' l r s xs =
  PP.nest 2 $ l <> PP.sep (PP.punctuate s xs) <> r


brackets :: [PP.Doc a] -> PP.Doc a
brackets = brackets' PP.lbracket PP.rbracket PP.comma


parens :: [PP.Doc a] -> PP.Doc a
parens = brackets' PP.lparen PP.rparen PP.comma


angles :: [PP.Doc a] -> PP.Doc a
angles = brackets' PP.langle PP.rangle PP.comma


braces :: [PP.Doc a] -> PP.Doc a
braces = brackets' PP.lbrace PP.rbrace PP.comma


prettyText :: PP.Pretty a => a -> T.Text
prettyText = PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions . PP.pretty
