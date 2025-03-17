module SF2TAL.Tal.Tal
  ( TName
  , Name
  , TSubst (..)
  , IsSubtyOf (..)
  , Ty (..)
  , THeap
  , TRegFile
  , R (..)
  , Val (..)
  , HVal (..)
  , Heaps
  , RegFile
  , Inst (..)
  , Seq (..)
  , Prog (..)
  , HasHeaps (..)
  , HasSeqs (..)
  , HasRegFile (..)
  )
where

import Data.Map qualified as M
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import SF2TAL.F (Prim (..))
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Utils


type TName = Int


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
  pretty = \case
    TVar a -> pp a
    TInt -> "int"
    TCode as trf -> "forall" <> brackets (fmap pp as) <> "." <+> ppMap ":" trf
    TTuple ts -> angles $ fmap (\(t, i) -> (if i then "" else "*") <> pp t) ts
    TExists a t -> "exists" <+> pp a <> "." <+> pp t


instance TSubst Ty where
  tsubst a t = \case
    TVar b
      | a == b -> t
      | otherwise -> TVar b
    TInt -> TInt
    TCode as trf -> TCode as $ tsubst a t trf
    TTuple ts -> TTuple (ts <&> _1 %~ tsubst a t)
    TExists b s -> TExists b $ tsubst a t s


-- | heap types
type THeap = M.Map Name Ty


-- | register file types
type TRegFile = M.Map R Ty


instance IsSubtyOf TRegFile where
  isSubtyOf = flip (M.isSubmapOfBy (flip isSubtyOf))


instance TSubst TRegFile where
  tsubst a t = fmap (tsubst a t)


-- | registers
data R
  = -- | Argument registers
    A Int
  | -- | Temporary registers
    R Int


deriving stock instance Show R


deriving stock instance Eq R


deriving stock instance Ord R


instance PP.Pretty R where
  pretty = \case
    A a -> pp $ "a" <> int2Text a
    R r -> pp $ "r" <> int2Text r


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
  pretty = \case
    Label l -> pp l
    IntLit i -> pp i
    Junk t -> "?" <> pp t
    Reg r -> pp r
    AppT w t -> pp w <> brackets [pp t]
    Pack t v t' -> "pack" <> brackets [pp t, pp v] <+> "as" <+> pp t'


instance TSubst Val where
  tsubst a b = \case
    Junk t -> Junk $ tsubst a b t
    v `AppT` t -> tsubst a b v `AppT` tsubst a b t
    Pack t v t' -> Pack (tsubst a b t) (tsubst a b v) (tsubst a b t')
    v -> v


-- | heap values
data HVal where
  -- | <vs>
  Tuple :: [Val] -> HVal
  -- | code[as]tregfile. seq
  Code :: [TName] -> TRegFile -> Seq -> HVal


deriving stock instance Show HVal


instance PP.Pretty HVal where
  pretty = \case
    Tuple vs -> angles $ fmap pp vs
    Code as tRegFile is ->
      nest $
        PP.vsep
          [ "code" <> brackets (fmap pp as) <> ppMap "=" tRegFile
          , pp is
          ]


-- | heaps
type Heaps = M.Map Name HVal


-- | register files
type RegFile = M.Map R Val


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


ppInst :: PP.Doc a -> [PP.Doc a] -> PP.Doc a
ppInst op rs = PP.hsep $ op : PP.punctuate "," rs


instance PP.Pretty Inst where
  pretty = \case
    Arith p rd rs v -> ppInst p' [pp rd, pp rs, pp v]
      where
        p' = case p of
          Add -> "add"
          Mul -> "mul"
          Sub -> "sub"
    Bnz r v -> ppInst "bnz" [pp r, pp v]
    Ld rd rs i -> ppInst "ld" [pp rd, pp rs <> brackets [pp i]]
    Malloc rd ts -> ppInst "malloc" [pp rd <> brackets (fmap pp ts)]
    Mov rd v -> ppInst "mov" [pp rd, pp v]
    St rd i rs -> ppInst "st" [pp rd <> brackets [pp i], pp rs]
    Unpack a rd v ->
      PP.hsep $ PP.punctuate "," ["unpack" <> brackets [pp a, pp rd], pp v]


instance TSubst Inst where
  tsubst a t = \case
    Arith p rd rs v -> Arith p rd rs (tsubst a t v)
    Malloc rd ts -> Malloc rd $ fmap (tsubst a t) ts
    Mov rd v -> Mov rd (tsubst a t v)
    Unpack b rd v -> Unpack b rd (tsubst a t v)
    i -> i


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
  pretty = \case
    Seq i is -> PP.vsep [pp i, pp is]
    Jmp v -> ppInst "jmp" [pp v]
    Halt t -> PP.hsep $ PP.punctuate "," ["halt" <> brackets [pp t]]


instance TSubst Seq where
  tsubst a t = \case
    Seq i is -> Seq (tsubst a t i) (tsubst a t is)
    Jmp v -> Jmp $ tsubst a t v
    Halt t' -> Halt $ tsubst a t t'


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
      [ ppMap "=" (p ^. heaps)
      , ppMap "=" (p ^. regFile)
      , pp (p ^. seqs)
      ]
