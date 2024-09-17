module SF2TAL.Tal.Tal
  ( TSubst (..)
  , IsSubtyOf (..)
  , Ty (..)
  , THeap
  , TRegFile
  , prettyMap
  , R
  , Val (..)
  , HVal (..)
  , Heaps
  , RegFile
  , Inst (..)
  , Seq (..)
  , Prog (..)
  )
where

import Data.HashMap.Strict qualified as HM
import Data.Text qualified as T
import Lens.Micro.Platform
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as PP
import SF2TAL.Common
import SF2TAL.F (Prim (..))


class TSubst a where
  tsubst :: TName -> Ty -> a -> a


class IsSubtyOf a where
  isSubtyOf :: a -> a -> Bool


-- | types
data Ty where
  -- | a
  TVar :: TName -> Ty
  -- | int
  TInt :: Ty
  -- | forall[as]. tregfile
  TCode :: [TName] -> TRegFile -> Ty
  -- | <ts>
  TTuple :: [(Ty, Bool)] -> Ty
  -- | exists a. t
  TExists :: TName -> Ty -> Ty


deriving stock instance Show Ty


instance Eq Ty where
  TVar a == TVar b = a == b
  TInt == TInt = True
  TCode [] trf == TCode [] trf' = trf == trf'
  TCode (a : as) trf == TCode (b : bs) trf' =
    TCode as trf == TCode bs (tsubst b (TVar a) trf')
  TTuple ss == TTuple ts = ss == ts
  TExists a s == TExists b t = s == tsubst b (TVar a) t
  _ == _ = False


instance IsSubtyOf Ty where
  TVar a `isSubtyOf` TVar b = a == b
  TInt `isSubtyOf` TInt = True
  TCode (a : as) trf `isSubtyOf` TCode (b : bs) trf' =
    TCode as trf `isSubtyOf` TCode bs (tsubst b (TVar a) trf')
  TTuple ss `isSubtyOf` TTuple ts =
    and $ zipWith (>=) (ss <&> (^. _2)) (ts <&> (^. _2))
  TExists a s `isSubtyOf` TExists b t = s == tsubst b (TVar a) t
  _ `isSubtyOf` _ = False


instance PP.Pretty Ty where
  pretty (TVar a) = pretty a
  pretty TInt = pretty ("int" :: T.Text)
  pretty (TCode as tRegFile) =
    pretty ("forall" :: T.Text)
      <> brackets (fmap pretty as)
      <> PP.dot
      <+> prettyMap PP.colon tRegFile
  pretty (TTuple ts) =
    angles $
      fmap
        ( \(t, i) ->
            (if i then mempty else pretty ("*" :: T.Text)) <> pretty t
        )
        ts
  pretty (TExists a t) =
    pretty ("exists" :: T.Text)
      <+> pretty a
      <> PP.dot
      <+> pretty t


instance TSubst Ty where
  tsubst a t (TVar b)
    | a == b = t
    | otherwise = TVar b
  tsubst _a _t TInt = TInt
  tsubst a t (TCode as tRegFile) = TCode as $ tsubst a t tRegFile
  tsubst a t (TTuple ts) = TTuple (ts <&> _1 %~ tsubst a t)
  tsubst a t (TExists b s) = TExists b $ tsubst a t s


-- | heap types
type THeap = HM.HashMap Name Ty


-- | register file types
type TRegFile = HM.HashMap R Ty


instance IsSubtyOf TRegFile where
  isSubtyOf = flip (HM.isSubmapOfBy (flip isSubtyOf))


prettyMap ::
  (PP.Pretty b, PP.Pretty c) => PP.Doc a -> HM.HashMap b c -> PP.Doc a
prettyMap s xs =
  braces $ [PP.hsep [pretty k, s, pretty v] | (k, v) <- HM.toList xs]


instance TSubst TRegFile where
  tsubst a t = fmap (tsubst a t)


-- | registers
type R = T.Text


-- | word values or small values
data Val where
  -- | l
  Label :: Name -> Val
  -- | i
  IntLit :: Int -> Val
  -- | ?t
  Junk :: Ty -> Val
  -- | r
  Reg :: R -> Val
  -- | v[t]
  AppT :: Val -> Ty -> Val
  -- | pack[t, v] as t'
  Pack :: Ty -> Val -> Ty -> Val


deriving stock instance Show Val


deriving stock instance Eq Val


instance PP.Pretty Val where
  pretty (Label l) = pretty l
  pretty (IntLit i) = pretty i
  pretty (Junk t) = pretty ("?" :: T.Text) <> pretty t
  pretty (Reg r) = pretty r
  pretty (AppT w t) = pretty w <> brackets [pretty t]
  pretty (Pack t v t') =
    pretty ("pack" :: T.Text)
      <> brackets [pretty t, pretty v]
      <+> pretty ("as" :: T.Text)
      <+> pretty t'


-- | heap values
data HVal where
  -- | <vs>
  Tuple :: [Val] -> HVal
  -- | code[as]tregfile. seq
  Code :: [TName] -> TRegFile -> Seq -> HVal


deriving stock instance Show HVal


instance PP.Pretty HVal where
  pretty (Tuple vs) = angles $ fmap pretty vs
  pretty (Code as tRegFile is) =
    PP.nest 2 $
      PP.vsep
        [ pretty ("code" :: T.Text)
            <> brackets (fmap pretty as)
            <> prettyMap PP.equals tRegFile
        , pretty is
        ]


-- | heaps
type Heaps = HM.HashMap Name HVal


-- | register files
type RegFile = HM.HashMap R Val


-- | instructions
data Inst where
  -- | (add|mul|sub) rd, rs, v
  Arith :: Prim -> R -> R -> Val -> Inst
  -- | bnz r, v
  Bnz :: R -> Val -> Inst
  -- | ld rd, rs[i]
  Ld :: R -> R -> Int -> Inst
  -- | malloc rd[ts]
  Malloc :: R -> [Ty] -> Inst
  -- | mov rd, v
  Mov :: R -> Val -> Inst
  -- | st rd[i], rs
  St :: R -> Int -> R -> Inst
  -- | unpack[a, rd], v
  Unpack :: TName -> R -> Val -> Inst


deriving stock instance Show Inst


prettyInst :: T.Text -> [PP.Doc a] -> PP.Doc a
prettyInst op rs = PP.hsep $ pretty op : PP.punctuate PP.comma rs


instance PP.Pretty Inst where
  pretty (Arith op rd rs v) = prettyInst op' [pretty rd, pretty rs, pretty v]
    where
      op' = case op of
        Add -> "add"
        Mul -> "mul"
        Sub -> "sub"
  pretty (Bnz r v) = prettyInst "bnz" [pretty r, pretty v]
  pretty (Ld rd rs i) =
    prettyInst "ld" [pretty rd, pretty rs <> brackets [pretty i]]
  pretty (Malloc rd ts) =
    prettyInst "malloc" [pretty rd <> brackets (fmap pretty ts)]
  pretty (Mov rd v) = prettyInst "mov" [pretty rd, pretty v]
  pretty (St rd i rs) =
    prettyInst "st" [pretty rd <> brackets [pretty i], pretty rs]
  pretty (Unpack a rd v) =
    PP.hsep $
      PP.punctuate
        PP.comma
        [pretty ("unpack" :: T.Text) <> brackets [pretty a, pretty rd], pretty v]


instance TSubst Inst where
  tsubst a t (Malloc rd ts) = Malloc rd $ fmap (tsubst a t) ts
  tsubst _ _ i = i


-- | instruction sequences
data Seq where
  -- | i; I
  Seq :: Inst -> Seq -> Seq
  -- | jmp v
  Jmp :: Val -> Seq
  -- | halt[t]
  Halt :: Ty -> Seq


infixr 5 `Seq`


deriving stock instance Show Seq


instance PP.Pretty Seq where
  pretty (Seq i is) = PP.vsep [pretty i, pretty is]
  pretty (Jmp v) = prettyInst "jmp" [pretty v]
  pretty (Halt t) =
    PP.hsep $ PP.punctuate PP.comma ["halt" <> brackets [pretty t]]


instance TSubst Seq where
  tsubst a t (Seq i is) = Seq (tsubst a t i) (tsubst a t is)
  tsubst _ _ (Jmp v) = Jmp v
  tsubst a t (Halt t') = Halt (tsubst a t t')


data Prog = Prog
  { heaps :: Heaps
  , regFile :: RegFile
  , seqs :: Seq
  }


deriving stock instance Show Prog


makeFieldsId ''Prog


instance PP.Pretty Prog where
  pretty p =
    parens
      [ prettyMap PP.equals (p ^. heaps)
      , prettyMap PP.equals (p ^. regFile)
      , pretty (p ^. seqs)
      ]
