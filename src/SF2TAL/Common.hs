module SF2TAL.Common
  ( classIdFields
  , makeFieldsId
  , int2Text
  , TName
  , Name
  , MonadUniq (..)
  , runUniqT
  , brackets
  , parens
  , angles
  , braces
  , prettyText
  )
where

import Control.Monad.State
import Data.Char
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


type TName = T.Text


type Name = T.Text


class Monad m => MonadUniq m where
  freshName :: m Name


type UniqT = StateT Int


instance Monad m => MonadUniq (UniqT m) where
  freshName = do
    n <- get
    modify (+ 1)
    pure $ T.pack $ "_" <> show n


runUniqT :: Monad m => UniqT m a -> m a
runUniqT m = evalStateT m 0


brackets' :: PP.Doc a -> PP.Doc a -> PP.Doc a -> [PP.Doc a] -> PP.Doc a
brackets' l r s xs =
  PP.cat [PP.nest 2 $ PP.vcat [l, PP.vsep $ PP.punctuate s xs], r]


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
