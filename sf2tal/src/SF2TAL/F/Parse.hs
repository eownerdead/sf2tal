module SF2TAL.F.Parse (parse) where

import Control.Monad.Combinators.Expr
import Data.Char
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import SF2TAL.F.F
import SF2TAL.Prelude hiding (try)
import Text.Megaparsec hiding (parse)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L


type Parser = Parsec Void T.Text


ws :: Parser ()
ws =
  L.space
    space1
    (L.skipLineComment "--")
    (L.skipBlockCommentNested "{-" "-}")


tok :: Parser a -> Parser a
tok p = p <* ws


reserved :: S.Set T.Text
reserved = S.fromList ["int", "at", "let", "and", "in", "if0", "then", "else"]


ident :: Parser (Name_ u)
ident = label "identifier" $ try do
  s <- tok $ T.cons <$> letterChar <*> takeWhileP Nothing isAlphaNum
  if S.member s reserved
    then unexpected $ Label $ NE.fromList $ "reserved word " <> T.unpack s
    else pure $ Name s 0


kw :: T.Text -> Parser ()
kw = void . tok . string


sym :: T.Text -> Parser ()
sym = void . L.symbol ws


tSimp :: Parser Ty
tSimp =
  choice
    [ TVar <$> ident
    , TInt <$ kw "int"
    , TTuple <$> between (sym "<") (sym ">") (sepEndBy ty (sym ","))
    , between (sym "(") (sym ")") ty
    ]


tOps :: Parser Ty
tOps =
  makeExprParser
    tSimp
    [[InfixR (TFun <$ sym "->")]]


ty :: Parser Ty
ty =
  label "type" . choice $
    [ TForall <$> (kw "forall" *> ident <* sym ".") <*> ty
    , tOps
    ]


int :: Parser Int
int = tok L.decimal <?> "integer literal"


simp :: Parser Tm
simp =
  choice
    [ Var <$> ident <*> pure Nothing
    , IntLit <$> int
    , Tuple <$> between (sym "(|") (sym "|)") (sepEndBy tm (sym ","))
    , between (sym "(") (sym ")") tm
    ]


app :: Parser Tm
app = foldl App <$> simp <*> many simp


ops :: Parser Tm
ops =
  makeExprParser
    app
    [ [Prefix (At <$> (kw "at" *> int))]
    , [InfixL (bin BMul "*")]
    ,
      [ InfixL (bin BAdd "+")
      , InfixL (bin BSub "-")
      ]
    ,
      [ InfixL (bin BEq "==")
      , InfixL (bin BNe "/=")
      , InfixL (bin BLe "<=")
      , InfixL (bin BLt "<")
      ]
    , [Postfix (flip Ann <$ sym ":" <*> ty)]
    ]
  where
    bin p s = BinOp p <$ sym s <?> "arithmetic operators"


letBody :: Parser (Name, Tm)
letBody = (,) <$> ident <* sym "=" <*> tm


tm :: Parser Tm
tm =
  Loc
    <$> getSourcePos
    <*> choice
      [ LetRec
          <$> (kw "let" *> (M.fromList <$> sepEndBy letBody (sym ";")))
          <* kw "in"
          <*> tm
      , Abs <$> (sym "\\" *> ident) <*> optional (sym ":" *> ty) <* sym "." <*> tm
      , If <$> (kw "if" *> tm) <*> (kw "then" *> tm) <*> (kw "else" *> tm)
      , ops
      ]
    <?> "expression"


parse :: T.Text -> Eff es Tm
parse s = case runParser (ws *> tm <* eof) "" s of
  Right x -> pure x
  Left e -> error $ errorBundlePretty e
