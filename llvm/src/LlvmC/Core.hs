module LlvmC.Core
  ( L.IntPredicate (.., IntEQ)
  , L.ContextRef
  , L.ModuleRef
  , L.TypeRef
  , L.ValueRef
  , L.BasicBlockRef
  , Context
  , Module
  , Builder
  , runContext
  , createModule
  , newFunction
  , defineFunction
  , getParams
  , int64Type
  , functionType
  , structType
  , pointerType
  , voidType
  , constInt
  , addIncoming
  , newBuilder
  , positionBuilderAtEnd
  , getInsertBlock
  , builderFunction
  , buildRet
  , buildBr
  , buildCondBr
  , buildAdd
  , buildSub
  , buildMul
  , buildMalloc
  , buildLoad2
  , buildStore
  , buildGEP2
  , buildICmp
  , buildPhi
  , buildCall2
  , defineBasicBlock
  , getBasicBlockParent
  , appendBasicBlock
  )
where

import Data.Text qualified as T
import Data.Text.Foreign qualified as T
import Effectful
import Effectful.Dispatch.Static
import Foreign
import Foreign.C.String (CString)
import LlvmC.Raw.Core qualified as L
import LlvmC.Raw.Types qualified as L
import System.IO.Unsafe (unsafePerformIO)


data Context :: Effect


type instance DispatchOf Context = Static NoSideEffects


newtype instance StaticRep Context = Context L.ContextRef


data Module :: Effect


type instance DispatchOf Module = Static NoSideEffects


newtype instance StaticRep Module = Module L.ModuleRef


data Builder :: Effect


type instance DispatchOf Builder = Static NoSideEffects


newtype instance StaticRep Builder = Builder L.BuilderRef


runContext :: IOE :> es => Eff (Context : es) a -> Eff es a
runContext f = do
  ctx <- liftIO L.contextCreate
  evalStaticRep (Context ctx) f


unsafeWithContext :: Context :> es => (L.ContextRef -> IO a) -> Eff es a
unsafeWithContext f = do
  Context ctx <- getStaticRep
  unsafeEff_ $ f ctx


createModule ::
  Context :> es => T.Text -> Eff (Module : es) a -> Eff es (a, L.ModuleRef)
createModule moduleId f = do
  Context c <- getStaticRep
  m <- unsafeEff_ $ T.withCString moduleId \ptr ->
    L.moduleCreateWithNameInContext ptr c
  r <- evalStaticRep (Module m) f
  pure (r, m)


newFunction :: Module :> es => T.Text -> L.TypeRef -> Eff es L.ValueRef
newFunction name ty = do
  Module m <- getStaticRep
  unsafeEff_ $ T.withCString name \ptr -> L.addFunction m ptr ty


defineFunction ::
  Context :> es =>
  L.ValueRef ->
  ([L.ValueRef] -> Eff (Builder : es) a) ->
  Eff es a
defineFunction fn f = do
  bb <- appendBasicBlock "entry" fn
  defineBasicBlock bb $ f (getParams fn)


getParams :: L.ValueRef -> [L.ValueRef]
getParams f = unsafePerformIO do
  len <- fromIntegral <$> L.countParams f
  allocaArray len \ptr -> do
    L.getParams f ptr
    peekArray len ptr


int64Type :: Context :> es => Eff es L.TypeRef
int64Type = unsafeWithContext L.int64TypeInContext


functionType ::
  Context :> es => Bool -> L.TypeRef -> [L.TypeRef] -> Eff es L.TypeRef
functionType varargs tRet tParams =
  unsafeEff_ $ withArrayLen tParams \len ptr ->
    L.functionType tRet ptr (fromIntegral len) (L.Bool $ fromBool varargs)


structType :: Context :> es => Bool -> [L.TypeRef] -> Eff es L.TypeRef
structType packed' ts =
  unsafeEff_ $ withArrayLen ts \len ptr ->
    L.structType ptr (fromIntegral len) (L.Bool $ fromBool packed')


pointerType :: Context :> es => Int -> Eff es L.TypeRef
pointerType addressSpace =
  unsafeWithContext \c -> L.pointerTypeInContext c (fromIntegral addressSpace)


voidType :: Context :> es => Eff es L.TypeRef
voidType = unsafeWithContext L.voidTypeInContext


-- Depends on context internally
constInt :: Context :> es => Bool -> L.TypeRef -> Word64 -> Eff es L.ValueRef
constInt signExtend intTy n =
  unsafeEff_ $ L.constInt intTy (fromIntegral n) (L.Bool $ fromBool signExtend)


addIncoming ::
  Context :> es => L.ValueRef -> [(L.ValueRef, L.BasicBlockRef)] -> Eff es ()
addIncoming phiNode incoming = do
  unsafeEff_ $ withArrayLen values \vlen vptr ->
    withArray blocks \bptr ->
      L.addIncoming phiNode vptr bptr (fromIntegral vlen)
  where
    (values, blocks) = unzip incoming


newBuilder :: Context :> es => Eff es L.BuilderRef
newBuilder = unsafeWithContext L.createBuilderInContext


positionBuilderAtEnd :: Builder :> es => L.BasicBlockRef -> Eff es ()
positionBuilderAtEnd block = do
  Builder b <- getStaticRep
  unsafeEff_ $ L.positionBuilderAtEnd b block


getInsertBlock :: Builder :> es => Eff es L.BasicBlockRef
getInsertBlock = do
  Builder b <- getStaticRep
  unsafeEff_ $ L.getInsertBlock b


builderFunction :: Builder :> es => Eff es L.ValueRef
builderFunction = getBasicBlockParent <$> getInsertBlock


buildRet :: Builder :> es => L.ValueRef -> Eff es L.ValueRef
buildRet v = do
  Builder b <- getStaticRep
  unsafeEff_ $ L.buildRet b v


buildBr :: Builder :> es => L.BasicBlockRef -> Eff es L.ValueRef
buildBr dest = do
  Builder b <- getStaticRep
  unsafeEff_ $ L.buildBr b dest


buildCondBr ::
  Builder :> es =>
  L.ValueRef ->
  L.BasicBlockRef ->
  L.BasicBlockRef ->
  Eff es L.ValueRef
buildCondBr if' then' else' = do
  Builder b <- getStaticRep
  unsafeEff_ $ L.buildCondBr b if' then' else'


withBin ::
  Builder :> es =>
  (L.BuilderRef -> L.ValueRef -> L.ValueRef -> CString -> IO L.ValueRef) ->
  T.Text ->
  L.ValueRef ->
  L.ValueRef ->
  Eff es L.ValueRef
withBin f name lhs rhs = do
  Builder b <- getStaticRep
  unsafeEff_ $ T.withCString name $ f b lhs rhs


buildAdd ::
  Builder :> es => T.Text -> L.ValueRef -> L.ValueRef -> Eff es L.ValueRef
buildAdd = withBin L.buildAdd


buildSub ::
  Builder :> es => T.Text -> L.ValueRef -> L.ValueRef -> Eff es L.ValueRef
buildSub = withBin L.buildSub


buildMul ::
  Builder :> es => T.Text -> L.ValueRef -> L.ValueRef -> Eff es L.ValueRef
buildMul = withBin L.buildMul


buildMalloc :: Builder :> es => T.Text -> L.TypeRef -> Eff es L.ValueRef
buildMalloc name ty = do
  Builder b <- getStaticRep
  unsafeEff_ $ T.withCString name $ L.buildMalloc b ty


buildLoad2 ::
  Builder :> es => T.Text -> L.TypeRef -> L.ValueRef -> Eff es L.ValueRef
buildLoad2 name ty pointerVal = do
  Builder b <- getStaticRep
  unsafeEff_ $ T.withCString name $ L.buildLoad2 b ty pointerVal


buildStore :: Builder :> es => L.ValueRef -> L.ValueRef -> Eff es L.ValueRef
buildStore val ptr = do
  Builder b <- getStaticRep
  unsafeEff_ $ L.buildStore b val ptr


buildGEP2 ::
  Builder :> es =>
  T.Text ->
  L.TypeRef ->
  L.ValueRef ->
  [L.ValueRef] ->
  Eff es L.ValueRef
buildGEP2 name ty constantVal constantIndices = do
  Builder b <- getStaticRep
  unsafeEff_ $ withArrayLen constantIndices \len ptr ->
    T.withCString name $ L.buildGEP2 b ty constantVal ptr (fromIntegral len)


buildICmp ::
  Builder :> es =>
  T.Text ->
  L.IntPredicate ->
  L.ValueRef ->
  L.ValueRef ->
  Eff es L.ValueRef
buildICmp name op lhs rhs = do
  Builder b <- getStaticRep
  unsafeEff_ $ T.withCString name $ L.buildICmp b op lhs rhs


buildPhi :: Builder :> es => T.Text -> L.TypeRef -> Eff es L.ValueRef
buildPhi name ty = do
  Builder b <- getStaticRep
  unsafeEff_ $ T.withCString name $ L.buildPhi b ty


buildCall2 ::
  Builder :> es =>
  T.Text ->
  L.TypeRef ->
  L.ValueRef ->
  [L.ValueRef] ->
  Eff es L.ValueRef
buildCall2 name ty fn args = do
  Builder b <- getStaticRep
  unsafeEff_ $ withArrayLen args \len ptr ->
    T.withCString name $ L.buildCall2 b ty fn ptr (fromIntegral len)


defineBasicBlock ::
  Context :> es => L.BasicBlockRef -> Eff (Builder : es) a -> Eff es a
defineBasicBlock bb f = do
  b <- newBuilder
  evalStaticRep (Builder b) do
    positionBuilderAtEnd bb
    f


getBasicBlockParent :: L.BasicBlockRef -> L.ValueRef
getBasicBlockParent bb = unsafePerformIO $ L.getBasicBlockParent bb


appendBasicBlock ::
  Context :> es => T.Text -> L.ValueRef -> Eff es L.BasicBlockRef
appendBasicBlock name fn = unsafeWithContext \ctx ->
  T.withCString name $ L.appendBasicBlockInContext ctx fn
