{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.Types where

import Data.Bits (FiniteBits)
import qualified Data.Bits as Bits
import qualified Data.Ix as Ix
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import Prelude (Bounded, Enum, Eq, Integral, Num, Ord, Read, Real, Show)

$(CAPI.addCSource "#define const\n")

newtype Bool = Bool
  { un_Bool :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

data OpaqueMemoryBuffer

newtype MemoryBufferRef = MemoryBufferRef
  { un_MemoryBufferRef :: F.Ptr OpaqueMemoryBuffer
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueContext

newtype ContextRef = ContextRef
  { un_ContextRef :: F.Ptr OpaqueContext
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueModule

newtype ModuleRef = ModuleRef
  { un_ModuleRef :: F.Ptr OpaqueModule
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueType

newtype TypeRef = TypeRef
  { un_TypeRef :: F.Ptr OpaqueType
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueValue

newtype ValueRef = ValueRef
  { un_ValueRef :: F.Ptr OpaqueValue
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueBasicBlock

newtype BasicBlockRef = BasicBlockRef
  { un_BasicBlockRef :: F.Ptr OpaqueBasicBlock
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueMetadata

newtype MetadataRef = MetadataRef
  { un_MetadataRef :: F.Ptr OpaqueMetadata
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueNamedMDNode

newtype NamedMDNodeRef = NamedMDNodeRef
  { un_NamedMDNodeRef :: F.Ptr OpaqueNamedMDNode
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data ValueMetadataEntry

data OpaqueBuilder

newtype BuilderRef = BuilderRef
  { un_BuilderRef :: F.Ptr OpaqueBuilder
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueDIBuilder

newtype DIBuilderRef = DIBuilderRef
  { un_DIBuilderRef :: F.Ptr OpaqueDIBuilder
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueModuleProvider

newtype ModuleProviderRef = ModuleProviderRef
  { un_ModuleProviderRef :: F.Ptr OpaqueModuleProvider
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaquePassManager

newtype PassManagerRef = PassManagerRef
  { un_PassManagerRef :: F.Ptr OpaquePassManager
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueUse

newtype UseRef = UseRef
  { un_UseRef :: F.Ptr OpaqueUse
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueOperandBundle

newtype OperandBundleRef = OperandBundleRef
  { un_OperandBundleRef :: F.Ptr OpaqueOperandBundle
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueAttributeRef

newtype AttributeRef = AttributeRef
  { un_AttributeRef :: F.Ptr OpaqueAttributeRef
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueDiagnosticInfo

newtype DiagnosticInfoRef = DiagnosticInfoRef
  { un_DiagnosticInfoRef :: F.Ptr OpaqueDiagnosticInfo
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data Comdat

newtype ComdatRef = ComdatRef
  { un_ComdatRef :: F.Ptr Comdat
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data ModuleFlagEntry

data OpaqueJITEventListener

newtype JITEventListenerRef = JITEventListenerRef
  { un_JITEventListenerRef :: F.Ptr OpaqueJITEventListener
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueBinary

newtype BinaryRef = BinaryRef
  { un_BinaryRef :: F.Ptr OpaqueBinary
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueDbgRecord

newtype DbgRecordRef = DbgRecordRef
  { un_DbgRecordRef :: F.Ptr OpaqueDbgRecord
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)
