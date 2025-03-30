module SF2TAL.F.Parse (parse) where

import Control.Exception.Safe hiding (try)
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Char
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Void
import Effectful
import SF2TAL.F.F
import SF2TAL.Name
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


tIdent :: Parser TName
tIdent = label "identifier" $ try do
  s <- tok $ T.cons <$> letterChar <*> takeWhileP Nothing isAlphaNum
  if S.member s reserved
    then unexpected $ Label $ NE.fromList $ "reserved word " <> T.unpack s
    else pure s


ident :: Parser Name
ident = Name <$> tIdent <*> pure 0


kw :: T.Text -> Parser ()
kw = void . tok . string


sym :: T.Text -> Parser ()
sym = void . L.symbol ws


tSimp :: Parser Ty
tSimp =
  choice
    [ TVar <$> tIdent
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
    [ TForall <$> (kw "forall" *> tIdent <* sym ".") <*> ty
    , tOps
    ]


int :: Parser Int
int = tok L.decimal <?> "integer literal"


simp :: Parser Tm
simp =
  choice
    [ Var <$> ident <*> pure Nothing
    , IntLit <$> int
    , Tuple <$> between (sym "<") (sym ">") (sepEndBy tm (sym ","))
    , between (sym "(") (sym ")") tm
    ]


app :: Parser Tm
app = foldl App <$> simp <*> many simp


ops :: Parser Tm
ops =
  makeExprParser
    app
    [ [Prefix (At <$> (kw "at" *> int))]
    , [InfixL (arith Mul "*")]
    ,
      [ InfixL (arith Add "+")
      , InfixL (arith Sub "-")
      ]
    , [Postfix (flip Ann <$ sym ":" <*> ty)]
    ]
  where
    arith p s = Arith p <$ sym s <?> "arithmetic operators"


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
      , If0 <$> (kw "if0" *> tm) <*> (kw "then" *> tm) <*> (kw "else" *> tm)
      , ops
      ]
    <?> "expression"


parse :: T.Text -> Eff es Tm
parse s = case runParser (ws *> tm <* eof) "" s of
  Right x -> pure x
  Left e -> throwString $ errorBundlePretty e
