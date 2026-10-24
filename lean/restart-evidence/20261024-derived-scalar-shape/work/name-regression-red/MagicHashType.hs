{-# LANGUAGE DeriveGeneric, MagicHash, TemplateHaskell #-}
module MagicHashType where
import Data.CFTA.TH (deriveNode)
data Hashy# = Constructor
$(deriveNode ''Hashy#)
