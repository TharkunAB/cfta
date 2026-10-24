{-# LANGUAGE DeriveGeneric, MagicHash, TemplateHaskell #-}
module Control where
import Data.CFTA.TH (deriveNode)
data Hashy = Constructor
$(deriveNode ''Hashy)
