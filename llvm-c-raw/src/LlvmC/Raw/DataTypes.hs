{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.DataTypes where

import qualified HsBindgen.Runtime.CAPI as CAPI

$(CAPI.addCSource "#define const\n")
