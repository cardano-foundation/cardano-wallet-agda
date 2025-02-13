module Cardano.Wallet.Deposit.Pure.Experimental where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub)
import Cardano.Wallet.Address.Encoding (NetworkTag, fromNetworkId)
import Cardano.Wallet.Deposit.Pure.Address (AddressState)
import qualified Cardano.Wallet.Deposit.Pure.Address as Addr
    ( fromXPubAndCount
    , getNetworkTag
    , getXPub
    , isOurs
    , listCustomers
    , newChangeAddress
    )
import Cardano.Wallet.Deposit.Pure.Address.Customer (Customer)
import qualified Cardano.Wallet.Deposit.Pure.Address.Customer as Addr
    ( deriveCustomerAddress
    )
import Cardano.Wallet.Deposit.Pure.TxSummary (TxSummary)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.Tx as UTxO (applyTx)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (empty)
import Cardano.Wallet.Deposit.Read.Temp (Address, TxBody)
import Cardano.Wallet.Read.Address ()
import Cardano.Wallet.Read.Block (Block, getEraTransactions)
import Cardano.Wallet.Read.Chain
    ( ChainPoint (GenesisPoint)
    , NetworkId (Mainnet)
    , Slot
    , getChainPoint
    , slotFromChainPoint
    )
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx (Tx, TxOut, mkBasicTxOut)
import Cardano.Wallet.Read.Value (Value)
import Cardano.Write.Tx.Balance
    ( ChangeAddressGen
    , PartialTx (PartialTxC)
    , balanceTransaction
    )
import qualified Data.Map as Map (Map, empty, lookup)
import Data.Word.Odd (Word31)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs regarding re-exports
import Cardano.Wallet.Deposit.Pure.Address
    ( AddressState
    , Customer
    )
import qualified Cardano.Wallet.Deposit.Pure.Address as Addr
import Cardano.Wallet.Deposit.Pure.TxSummary
    ( TxSummary
    )
import qualified Cardano.Wallet.Deposit.Pure.UTxO.Tx as UTxO
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO
    ( UTxO
    )
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO

data WalletState = WalletState
    { addresses :: AddressState
    , utxo :: UTxO
    , txSummaries :: Map.Map Customer [TxSummary]
    , localTip :: ChainPoint
    }

getXPub :: WalletState -> XPub
getXPub = Addr.getXPub . \r -> addresses r

defaultNetworkId :: NetworkId
defaultNetworkId = Mainnet

getNetworkTag :: WalletState -> NetworkTag
getNetworkTag s = Addr.getNetworkTag (addresses s)

deriveCustomerAddress :: XPub -> Customer -> Address
deriveCustomerAddress =
    Addr.deriveCustomerAddress (fromNetworkId defaultNetworkId)

fromXPubAndCount :: XPub -> Word31 -> WalletState
fromXPubAndCount xpub count =
    WalletState
        (Addr.fromXPubAndCount defaultNetworkId xpub count)
        UTxO.empty
        Map.empty
        GenesisPoint

listCustomers :: WalletState -> [(Customer, Address)]
listCustomers = Addr.listCustomers . \r -> addresses r

knownCustomerAddress :: Address -> WalletState -> Bool
knownCustomerAddress a =
    elem a . map (\r -> snd r) . listCustomers

isOurs :: WalletState -> Address -> Bool
isOurs s = Addr.isOurs (addresses s)

getWalletSlot :: WalletState -> Slot
getWalletSlot = slotFromChainPoint . \r -> localTip r

applyTx
    :: IsEra era => ChainPoint -> Tx era -> WalletState -> WalletState
applyTx point tx s0 = s1
  where
    s1 :: WalletState
    s1 =
        WalletState
            (addresses s0)
            (snd (UTxO.applyTx (isOurs s0) tx (utxo s0)))
            (txSummaries s0)
            point

-- |
-- Roll the 'WalletState' forward by one block.
rollForwardOne
    :: IsEra era => Block era -> WalletState -> WalletState
rollForwardOne block s0 =
    WalletState (addresses s1) (utxo s1) (txSummaries s1) point
  where
    point :: ChainPoint
    point = getChainPoint block
    s1 :: WalletState
    s1 =
        foldl
            (\s tx -> applyTx point tx s)
            s0
            (getEraTransactions block)

getCustomerHistory :: WalletState -> Customer -> [TxSummary]
getCustomerHistory s c = concat (Map.lookup c (txSummaries s))

totalUTxO :: WalletState -> UTxO
totalUTxO = \r -> utxo r

newChangeAddress :: WalletState -> ChangeAddressGen ()
newChangeAddress = Addr.newChangeAddress . \r -> addresses r

txOutFromPair :: (Address, Value) -> TxOut
txOutFromPair (x, y) = mkBasicTxOut x y

createPayment :: [(Address, Value)] -> WalletState -> Maybe TxBody
createPayment destinations s =
    balanceTransaction (utxo s) (newChangeAddress s) () partialTx
  where
    partialTx :: PartialTx
    partialTx = PartialTxC (map txOutFromPair destinations)
