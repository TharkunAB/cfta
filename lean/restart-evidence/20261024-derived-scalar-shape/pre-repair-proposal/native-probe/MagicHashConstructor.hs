{-# LANGUAGE DeriveGeneric, MagicHash, TemplateHaskell #-}
module MagicHashConstructor where
import Data.CFTA.TH (deriveNode)
data Hashy = Constructor#
$(deriveNode ''Hashy)
