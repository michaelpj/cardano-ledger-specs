{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- The STS instance for UTXOW is technically an orphan.
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.ShelleyMA.Rules.Utxow where

import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CryptoClass
import Cardano.Ledger.Era (Era (Crypto))
import Cardano.Ledger.Shelley (ShelleyBased)
import Cardano.Ledger.ShelleyMA (MaryOrAllegra, ShelleyMAEra)
import Cardano.Ledger.ShelleyMA.Value (Value, policies, policyID)
import Control.State.Transition.Extended
import Data.Foldable (Foldable (toList))
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import Data.Relation (Relation ((◁)))
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import GHC.Records (HasField (..))
import Shelley.Spec.Ledger.BaseTypes
import Shelley.Spec.Ledger.Delegation.Certificates (requiresVKeyWitness)
import Shelley.Spec.Ledger.Keys (DSignable, Hash)
import Shelley.Spec.Ledger.LedgerState (UTxOState)
import Shelley.Spec.Ledger.MetaData
import Shelley.Spec.Ledger.PParams
import Shelley.Spec.Ledger.STS.Utxo
import Shelley.Spec.Ledger.STS.Utxow (UTXOW, UtxowPredicateFailure, initialLedgerStateUTXOW, utxoWitnessed)
import Shelley.Spec.Ledger.Scripts (ScriptHash)
import Shelley.Spec.Ledger.Tx (Tx (_body))
import Shelley.Spec.Ledger.TxBody
  ( DCert,
    EraIndependentTxBody,
    RewardAcnt (getRwdCred),
    TxIn,
    TxOut (TxOut),
    Wdrl (unWdrl),
  )
import Shelley.Spec.Ledger.UTxO
  ( UTxO (UTxO),
    getScriptHash,
    scriptCred,
    scriptStakeCred,
    txinsScript,
  )

-- | Computes the set of script hashes required to unlock the transaction inputs
-- and the withdrawals.
scriptsNeeded ::
  ( ShelleyBased era,
    Core.Value era ~ Value era,
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert era)),
    HasField "wdrls" (Core.TxBody era) (Wdrl era),
    HasField "inputs" (Core.TxBody era) (Set (TxIn era)),
    HasField "forge" (Core.TxBody era) (Core.Value era)
  ) =>
  UTxO era ->
  Tx era ->
  Set (ScriptHash era)
scriptsNeeded u tx =
  Set.fromList (Map.elems $ Map.mapMaybe (getScriptHash . unTxOut) u'')
    `Set.union` Set.fromList
      ( Maybe.mapMaybe (scriptCred . getRwdCred) $
          Map.keys withdrawals
      )
    `Set.union` Set.fromList
      ( Maybe.mapMaybe
          scriptStakeCred
          (filter requiresVKeyWitness certificates)
      )
    `Set.union` ((policyID `Set.map` (policies $ getField @"forge" txb)))
  where
    txb = _body tx
    unTxOut (TxOut a _) = a
    withdrawals = unWdrl $ getField @"wdrls" txb
    UTxO u'' = (txinsScript (getField @"inputs" txb) u) ◁ u
    certificates = (toList . getField @"certs") txb

--------------------------------------------------------------------------------
-- UTXOW STS
--------------------------------------------------------------------------------

instance
  ( CryptoClass.Crypto c,
    Typeable ma,
    ShelleyBased (ShelleyMAEra ma c)
  ) =>
  STS (UTXOW (ShelleyMAEra (ma :: MaryOrAllegra) c))
  where
  type State (UTXOW (ShelleyMAEra ma c)) = UTxOState (ShelleyMAEra ma c)
  type Signal (UTXOW (ShelleyMAEra ma c)) = Tx (ShelleyMAEra ma c)
  type Environment (UTXOW (ShelleyMAEra ma c)) = UtxoEnv (ShelleyMAEra ma c)
  type BaseM (UTXOW (ShelleyMAEra ma c)) = ShelleyBase
  type
    PredicateFailure (UTXOW (ShelleyMAEra ma c)) =
      UtxowPredicateFailure (ShelleyMAEra ma c)
  transitionRules = [utxoWitnessed scriptsNeeded]
  initialRules = [initialLedgerStateUTXOW]

instance
  (CryptoClass.Crypto c) =>
  Embed (UTXO (ShelleyMAEra ma c)) (UTXOW (ShelleyMAEra ma c))
  where
  wrapFailed = UtxoFailure
