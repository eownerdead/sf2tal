module SF2TAL.PP
  ( (PP.<+>)
  , pp
  , nest
  , brackets
  , parens
  , angles
  , braces
  , ppMap
  , docStr
  , docText
  , prettyText
  )
where

import Data.Map qualified as M
import Data.Text qualified as T
import Prettyprinter qualified as PP
import Prettyprinter.Render.String qualified as PP
import Prettyprinter.Render.Text qualified as PP


pp :: PP.Pretty a => a -> PP.Doc ann
pp = PP.pretty


nest :: PP.Doc ann -> PP.Doc ann
nest = PP.nest 2


brackets' :: PP.Doc a -> PP.Doc a -> PP.Doc a -> [PP.Doc a] -> PP.Doc a
brackets' l r s xs = nest $ l <> PP.sep (PP.punctuate s xs) <> r


brackets :: [PP.Doc a] -> PP.Doc a
brackets = brackets' PP.lbracket PP.rbracket PP.comma


parens :: [PP.Doc a] -> PP.Doc a
parens = brackets' PP.lparen PP.rparen PP.comma


angles :: [PP.Doc a] -> PP.Doc a
angles = brackets' PP.langle PP.rangle PP.comma


braces :: [PP.Doc a] -> PP.Doc a
braces = brackets' PP.lbrace PP.rbrace PP.comma


ppMap ::
  (PP.Pretty b, PP.Pretty c) => PP.Doc a -> M.Map b c -> PP.Doc a
ppMap s xs = braces $ [PP.hsep [pp k, s, pp v] | (k, v) <- M.toList xs]


docStr :: PP.Doc ann -> String
docStr = PP.renderString . PP.layoutPretty PP.defaultLayoutOptions


docText :: PP.Doc ann -> T.Text
docText = PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions


prettyText :: PP.Pretty a => a -> T.Text
prettyText = docText . pp
