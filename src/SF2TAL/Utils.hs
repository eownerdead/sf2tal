module SF2TAL.Utils
  ( module SF2TAL.Log
  , classIdFields
  , makeFieldsId
  , int2Text
  , universeOf
  , universeOnOf
  )
where

import Control.Applicative
import Data.Char
import Data.Coerce
import Data.Monoid
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
import Data.Text.Lazy.Builder qualified as LT
import Data.Text.Lazy.Builder.Int qualified as LT
import Language.Haskell.TH qualified as TH
import Lens.Micro.Platform
import SF2TAL.Log


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
