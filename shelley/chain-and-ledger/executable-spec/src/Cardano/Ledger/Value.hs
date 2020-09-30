{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Cardano.Ledger.Value where

{-
  ( PolicyID (..),
    AssetID (..),
    Value (..),
    pointWise,
    lookup,
    insert,
    insert2,
    modify,
  )
  -}

import Cardano.Binary
  ( FromCBOR,
    ToCBOR,
    encodeListLen,
    fromCBOR,
    toCBOR,
  )
import Cardano.Ledger.Crypto
import Cardano.Ledger.Era (Era)
import Cardano.Ledger.Val
  ( LabeledInt (..),
    Val (..),
    addrHashLen,
    assetIdLen,
    insertWithV,
    mapV,
    pointWiseM,
    scale,
    uint,
    unionWithV,
  )
import Cardano.Prelude (NFData (rnf), NoUnexpectedThunks (..), UseIsNormalFormNamed (..))
import Data.ByteString (ByteString)
import qualified Data.Map.Strict as Map
import Data.String (fromString)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Scripts (ScriptHash (..))
import Shelley.Spec.Ledger.Serialization (decodeRecordNamed)
import Prelude hiding (lookup)

-- ============================================================================
-- Multi Assests
--
-- A Value is a map from 'PolicyID's to a quantity of assets with this policy.
-- This map implements a finitely supported functions over PolicyId. A PolicyID
-- is not stored in the Map, then its quantity is assumed to be 0.
--
-- Operations on assets are usually implemented 'pointwise'. That is, we apply
-- the operation to the quantities for each asset in turn. So when we add two
-- 'Value's the resulting 'Value' has, for each asset, the sum of the quantities
-- of /that particular/ asset in the argument 'Value'. The effect of this is
-- that the assets in the 'Value' are "independent", and are operated on
-- separately.
--
-- We can think of 'Value' as a vector space whose dimensions are assets. At the
-- moment there is only a single asset type (Ada), so 'Value' contains
-- one-dimensional vectors. When asset-creating transactions are implemented,
-- this will change and the definition of 'Value' will change to a 'Map Asset
-- Int', effectively a vector with infinitely many dimensions whose non-zero
-- values are recorded in the map.
--
-- To create a value of 'Value', we need to specifiy an asset policy. This can
-- be done using 'Ledger.Ada.adaValueOf'. To get the ada dimension of 'Value' we
-- use 'Ledger.Ada.fromValue'. Plutus contract authors will be able to define
-- modules similar to 'Ledger.Ada' for their own assets.
-- ============================================================================

-- | Asset ID
newtype AssetID = AssetID {assetID :: ByteString}
  deriving newtype
    ( Show,
      Eq,
      ToCBOR,
      FromCBOR,
      Ord,
      NoUnexpectedThunks,
      NFData
    )

-- | Policy ID
newtype PolicyID era = PolicyID {policyID :: ScriptHash era}
  deriving (Show, Eq, ToCBOR, FromCBOR, Ord, NoUnexpectedThunks, NFData)

-- =========================================================================
-- The Value type, and a few of its instances

-- | The Value representing MultiAssets
data Value era = Value !Integer !(Map.Map (PolicyID era) (Map.Map AssetID Integer))
  deriving (Show, Generic)

instance Eq (Value era) where
  (Value c1 m1) == (Value c2 m2) = c1 == c2 && pointWiseM (==) m1 m2

instance Typeable era => Monoid (Value era) where
  mempty = Value 0 Map.empty

instance Typeable era => Semigroup (Value era) where
  (Value c1 m1) <> (Value c2 m2) = Value (plusLI c1 c2) (plusLI m1 m2)

instance NFData (Value era) where
  rnf !(Value c m) = seq (rnf c) (rnf m)

deriving via UseIsNormalFormNamed "Value" (Value era) instance NoUnexpectedThunks (Value era)

-- CBOR
instance
  (Crypto era, Era era) =>
  ToCBOR (Value era)
  where
  toCBOR (Value c v) =
    encodeListLen 2
      <> toCBOR c
      <> toCBOR v

instance
  (Crypto era, Era era) =>
  FromCBOR (Value era)
  where
  fromCBOR = do
    decodeRecordNamed (fromString "Value") (const 2) $ do
      c <- fromCBOR
      v <- fromCBOR
      pure $ Value c v

-- =========================================================================
-- The important LabeledInt and Val instances

-- This instance is a hand-encoding of the Binary Path instance.

instance (Era era, Crypto era, Typeable era) => LabeledInt (Value era) where
  zeroLI = Value 0 Map.empty
  scaleLI s (Value c v) = Value (scaleLI s c) (mapV (mapV (scaleLI s)) v)
  plusLI (Value c1 m1) (Value c2 m2) = Value (plusLI c1 c2) (plusLI m1 m2)
  isZeroLI (Value c m) = isZeroLI c && isZeroLI m
  pointWiseLI p (Value c m) (Value d n) = (pointWiseLI p c d) && (pointWiseLI p m n)

instance (Era era, Crypto era, Typeable era) => Val (Value era) where
  coin (Value c _) = Coin c
  inject (Coin c) = Value c Map.empty
  modifyCoin f (Value c m) = Value d m where (Coin d) = f (Coin c)
  size (Value _ v) =
    -- add uint for the Coin portion in this size calculation
    foldr accum uint v
    where
      -- add addrHashLen for each Policy ID
      accum u ans = foldr accumIns (ans + addrHashLen) u
        where
          -- add assetIdLen and uint for each asset of that Policy ID
          accumIns _ ans1 = ans1 + assetIdLen + uint

-- ========================================================================
-- Operations on Values

lookup :: PolicyID era -> AssetID -> Value era -> Integer
lookup pid aid (Value _ m) =
  case Map.lookup pid m of
    Nothing -> 0
    Just m2 -> Map.findWithDefault 0 aid m2

insert :: (Integer -> Integer -> Integer) -> PolicyID era -> AssetID -> Integer -> Value era -> Value era
insert combine pid aid new (Value c m1) =
  case Map.lookup pid m1 of
    Nothing -> Value c (insertWithV (plusLI) pid (insertWithV combine aid new zeroLI) m1)
    Just m2 -> case Map.lookup aid m2 of
      Nothing -> Value c (insertWithV plusLI pid (Map.singleton aid new) m1)
      Just old -> Value c (insertWithV plusLI pid (insertWithV combine aid (combine old new) m2) m1)

-- Might be useful to benchmark 'insert' vs 'insert2'
insert2 :: (Integer -> Integer -> Integer) -> PolicyID era -> AssetID -> Integer -> Value era -> Value era
insert2 combine pid aid new (Value c m1) = Value c (unionWithV (unionWithV combine) m1 (Map.singleton pid (Map.singleton aid new)))