module Cardano.Wallet.Deposit.Pure.Experimental where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub)
import Cardano.Wallet.Address.Encoding (NetworkTag)
import Cardano.Wallet.Deposit.Pure.Address (AddressState, Customer)
import qualified Cardano.Wallet.Deposit.Pure.Address as Addr
    ( createAddress
    , getNetworkTag
    , getXPub
    , isOurs
    , listCustomers
    , newChangeAddress
    )
import Cardano.Wallet.Deposit.Pure.TxSummary (TxSummary)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.Tx as UTxO (applyTx)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (balance)
import Cardano.Wallet.Deposit.Read.Temp (Address, TxBody)
import Cardano.Wallet.Read.Block (Block, getEraTransactions)
import Cardano.Wallet.Read.Chain (ChainPoint, getChainPoint)
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx (Tx, TxOut, mkBasicTxOut)
import Cardano.Wallet.Read.Value (Value)
import Cardano.Write.Tx.Balance
    ( ChangeAddressGen
    , PartialTx (PartialTxC)
    , balanceTransaction
    )
import qualified Haskell.Data.Map as Map (Map, lookup)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.
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

getNetworkTag :: WalletState -> NetworkTag
getNetworkTag s = Addr.getNetworkTag (addresses s)

listCustomers :: WalletState -> [(Customer, Address)]
listCustomers = Addr.listCustomers . \r -> addresses r

createAddress :: Customer -> WalletState -> (Address, WalletState)
createAddress c s0 = (addr, s1)
  where
    pair :: (Address, AddressState)
    pair = Addr.createAddress c (addresses s0)
    a1 :: AddressState
    a1 = snd pair
    addr :: Address
    addr = fst pair
    s1 :: WalletState
    s1 = WalletState a1 (utxo s0) (txSummaries s0) (localTip s0)

isOurs :: WalletState -> Address -> Bool
isOurs s = Addr.isOurs (addresses s)

knownCustomerAddress :: Address -> WalletState -> Bool
knownCustomerAddress address =
    elem address . map (\r -> snd r) . listCustomers

newChangeAddress :: WalletState -> ChangeAddressGen ()
newChangeAddress = Addr.newChangeAddress . \r -> addresses r

getCustomerHistory :: WalletState -> Customer -> [TxSummary]
getCustomerHistory s c = concat (Map.lookup c (txSummaries s))

availableBalance :: WalletState -> Value
availableBalance = UTxO.balance . \r -> utxo r

applyTx :: IsEra era => Tx era -> WalletState -> WalletState
applyTx tx s0 = s1
  where
    s1 :: WalletState
    s1 =
        WalletState
            (addresses s0)
            (snd (UTxO.applyTx (isOurs s0) tx (utxo s0)))
            (txSummaries s0)
            (localTip s0)

rollForwardOne
    :: IsEra era => Block era -> WalletState -> WalletState
rollForwardOne block s0 =
    WalletState
        (addresses s1)
        (utxo s1)
        (txSummaries s1)
        (getChainPoint block)
  where
    s1 :: WalletState
    s1 = foldl (\s tx -> applyTx tx s) s0 (getEraTransactions block)

txOutFromPair :: (Address, Value) -> TxOut
txOutFromPair (x, y) = mkBasicTxOut x y

createPayment :: [(Address, Value)] -> WalletState -> Maybe TxBody
createPayment destinations s =
    balanceTransaction (utxo s) (newChangeAddress s) () partialTx
  where
    partialTx :: PartialTx
    partialTx = PartialTxC (map txOutFromPair destinations)
