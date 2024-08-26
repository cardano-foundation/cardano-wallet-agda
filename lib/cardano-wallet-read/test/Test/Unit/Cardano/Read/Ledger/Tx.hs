{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Example transactions for testing.
-}
module Test.Unit.Cardano.Read.Ledger.Tx
    ( byronTx
    , shelleyTx
    , allegraTx
    , maryTx
    , maryTxLongOutput
    , alonzoTx
    , babbageTx
    , conwayTx
    ) where

import Prelude

import Cardano.Read.Ledger.Eras
    ( Allegra
    , Alonzo
    , Babbage
    , Byron
    , Conway
    , IsEra
    , Mary
    , Shelley
    )
import Cardano.Read.Ledger.Tx.CBOR
    ( deserializeTx
    )
import Cardano.Read.Ledger.Tx.Tx
    ( Tx
    )
import Data.ByteArray.Encoding
    ( Base (..)
    , convertFromBase
    )
import Data.ByteString
    ( ByteString
    )
import Data.ByteString.Lazy
    ( fromStrict
    )

import qualified Data.ByteString.Lazy as BL

{-----------------------------------------------------------------------------
    Test
------------------------------------------------------------------------------}

-- This transaction was assembled from the CBOR using
-- https://github.com/IntersectMBO/cardano-ledger
--   /blob/0a098670a7cf0d084c4087d4140f704f82784977
--      /eras/byron/ledger/impl/test/golden/cbor/utxo/Tx
--      /eras/byron/ledger/impl/test/golden/cbor/utxo/TxWitness
byronTx :: Tx Byron
byronTx = unsafeParseEraTxFromHex
    "82839f8200d81858258258204ba839c420b3d2bd439530f891cae9\
    \a5d4c4d812044630dac72e8e0962feeecc182fff9f8282d8185821\
    \83581caa5372095aaa680d19d4ca496983a145709c3be18b0d4c83\
    \cb7bdc5ea0001a32dc988e182fffa0818200D81858858258404B6D\
    \7977346C4453453553346653483665744E6F756958657A4379456A\
    \4B63337447346A61306B466A4F38717A616932365A4D5055454A66\
    \457931356F78356B5840688AAD857BC7FF30FC6862DA1BE281F420\
    \C65271B76AB19782FF40E2955AF88819C38E5C79138F28073ABAE1\
    \52C882258B4420A0C1C9FDD26C98812697FC3E00\
    \"

shelleyTx :: Tx Shelley
shelleyTx = unsafeParseEraTxFromHex
    "83a400828258200000000000000000000000000000000000000000\
    \000000000000000000000000008258200000000000000000000000\
    \000000000000000000000000000000000000000000010183825839\
    \010202020202020202020202020202020202020202020202020202\
    \020202020202020202020202020202020202020202020202020202\
    \0202021a005b8d8082583901030303030303030303030303030303\
    \030303030303030303030303030303030303030303030303030303\
    \03030303030303030303030303031a005b8d808258390104040404\
    \040404040404040404040404040404040404040404040404040404\
    \040404040404040404040404040404040404040404040404041a00\
    \7801e0021a0002102003191e46a10282845820130ae82201d7072e\
    \6fbfc0a1884fb54636554d14945b799125cf7ce38d477f51584058\
    \35ff78c6fc5e4466a179ca659fa85c99b8a3fba083f3f3f42ba360\
    \d479c64ef169914b52ade49b19a7208fd63a6e67a19c406b482660\
    \8fdc5307025506c307582001010101010101010101010101010101\
    \0101010101010101010101010101010144a1024100845820010000\
    \000000000000000000000000000000000000000000000000000000\
    \00005840e8e769ecd0f3c538f0a5a574a1c881775f086d6f4c845b\
    \81be9b78955728bffa7efa54297c6a5d73337bd6280205b1759c13\
    \f79d4c93f29871fc51b78aeba80e58200000000000000000000000\
    \00000000000000000000000000000000000000000044a1024100f6"

allegraTx :: Tx Allegra
allegraTx = unsafeParseEraTxFromHex
    "83a400828258200000000000000000000000000000000000000000\
    \000000000000000000000000008258200000000000000000000000\
    \000000000000000000000000000000000000000000010183825839\
    \010202020202020202020202020202020202020202020202020202\
    \020202020202020202020202020202020202020202020202020202\
    \0202021a005b8d8082583901030303030303030303030303030303\
    \030303030303030303030303030303030303030303030303030303\
    \03030303030303030303030303031a005b8d808258390104040404\
    \040404040404040404040404040404040404040404040404040404\
    \040404040404040404040404040404040404040404040404041a00\
    \7801e0021a0002102003191e46a10282845820130ae82201d7072e\
    \6fbfc0a1884fb54636554d14945b799125cf7ce38d477f51584058\
    \35ff78c6fc5e4466a179ca659fa85c99b8a3fba083f3f3f42ba360\
    \d479c64ef169914b52ade49b19a7208fd63a6e67a19c406b482660\
    \8fdc5307025506c307582001010101010101010101010101010101\
    \0101010101010101010101010101010144a1024100845820010000\
    \000000000000000000000000000000000000000000000000000000\
    \00005840e8e769ecd0f3c538f0a5a574a1c881775f086d6f4c845b\
    \81be9b78955728bffa7efa54297c6a5d73337bd6280205b1759c13\
    \f79d4c93f29871fc51b78aeba80e58200000000000000000000000\
    \00000000000000000000000000000000000000000044a1024100f6"

maryTx :: Tx Mary
maryTx = unsafeParseEraTxFromHex
    "83a400828258200000000000000000000000000000000000000000\
    \000000000000000000000000008258200000000000000000000000\
    \000000000000000000000000000000000000000000010183825839\
    \010202020202020202020202020202020202020202020202020202\
    \020202020202020202020202020202020202020202020202020202\
    \0202021a005b8d8082583901030303030303030303030303030303\
    \030303030303030303030303030303030303030303030303030303\
    \03030303030303030303030303031a005b8d808258390104040404\
    \040404040404040404040404040404040404040404040404040404\
    \040404040404040404040404040404040404040404040404041a00\
    \7801e0021a0002102003191e46a10282845820130ae82201d7072e\
    \6fbfc0a1884fb54636554d14945b799125cf7ce38d477f51584058\
    \35ff78c6fc5e4466a179ca659fa85c99b8a3fba083f3f3f42ba360\
    \d479c64ef169914b52ade49b19a7208fd63a6e67a19c406b482660\
    \8fdc5307025506c307582001010101010101010101010101010101\
    \0101010101010101010101010101010144a1024100845820010000\
    \000000000000000000000000000000000000000000000000000000\
    \00005840e8e769ecd0f3c538f0a5a574a1c881775f086d6f4c845b\
    \81be9b78955728bffa7efa54297c6a5d73337bd6280205b1759c13\
    \f79d4c93f29871fc51b78aeba80e58200000000000000000000000\
    \00000000000000000000000000000000000000000044a1024100f6"

{- Interesting example of a transaction on Mainnet in the Mary era.

The address of the first output of this transaction
has more bytes than are parsed by the ledger
— the ledger silently discards extra bytes at the end of the address.
In other words, serializing the address after parsing
will give a different result than the bytes recorded here.

See also
https://github.com/IntersectMBO/cardano-ledger/commit/ca351b80a7977a45cf4bcb9028b0a87436d2f448
-}
maryTxLongOutput :: Tx Mary
maryTxLongOutput = unsafeParseEraTxFromHex
    "83a40083825820bf4f8f6287993e17f785c949ef287416ba784198\
    \bb0ee12b2c7720cbffecd26f0082582052cf971bee4ba1b4e3b32b\
    \762e0bc3f7af83700bc8897eddbd77bd425dd28e8300825820bf4f\
    \8f6287993e17f785c949ef287416ba784198bb0ee12b2c7720cbff\
    \ecd26f01018282584e015bad085057ac10ecc7060f7ac41edd6f63\
    \068d8963ef7d86ca58669e5ecf2d283418a60be5a848a2380eb721\
    \000da1e0bbf39733134beca4cb57afb0b35fc89c63061c9914e055\
    \001a518c75161a035377d082583901f4e9e89cc628b9204fd6e2f4\
    \ae3e875aa0591fc2eb45b721520d2d22f4e9e89cc628b9204fd6e2\
    \f4ae3e875aa0591fc2eb45b721520d2d221a2c651d70021a000315\
    \70031a05f5e100a10083825820ec791e29bdb3157589872d3678db\
    \93f661d72ac18204759fa5e8d630eee1e66a58408944366b1015ee\
    \38809356ec48a59277701d40772a232c7cbb1e9510f2c632537d16\
    \318ba30a06953401dc2bfd693a34dc73d482050e6ccdea5811d0e1\
    \e32507825820ec791e29bdb3157589872d3678db93f661d72ac182\
    \04759fa5e8d630eee1e66a58408944366b1015ee38809356ec48a5\
    \9277701d40772a232c7cbb1e9510f2c632537d16318ba30a069534\
    \01dc2bfd693a34dc73d482050e6ccdea5811d0e1e32507825820ec\
    \791e29bdb3157589872d3678db93f661d72ac18204759fa5e8d630\
    \eee1e66a58408944366b1015ee38809356ec48a59277701d40772a\
    \232c7cbb1e9510f2c632537d16318ba30a06953401dc2bfd693a34\
    \dc73d482050e6ccdea5811d0e1e32507f6"

alonzoTx :: Tx Alonzo
alonzoTx = unsafeParseEraTxFromHex
    "84a400828258200000000000000000000000000000000000000000\
    \000000000000000000000000008258200000000000000000000000\
    \000000000000000000000000000000000000000000010183825839\
    \010202020202020202020202020202020202020202020202020202\
    \020202020202020202020202020202020202020202020202020202\
    \0202021a005b8d8082583901030303030303030303030303030303\
    \030303030303030303030303030303030303030303030303030303\
    \03030303030303030303030303031a005b8d808258390104040404\
    \040404040404040404040404040404040404040404040404040404\
    \040404040404040404040404040404040404040404040404041a00\
    \7801e0021a0002102003191e46a10282845820130ae82201d7072e\
    \6fbfc0a1884fb54636554d14945b799125cf7ce38d477f51584058\
    \35ff78c6fc5e4466a179ca659fa85c99b8a3fba083f3f3f42ba360\
    \d479c64ef169914b52ade49b19a7208fd63a6e67a19c406b482660\
    \8fdc5307025506c307582001010101010101010101010101010101\
    \0101010101010101010101010101010144a1024100845820010000\
    \000000000000000000000000000000000000000000000000000000\
    \00005840e8e769ecd0f3c538f0a5a574a1c881775f086d6f4c845b\
    \81be9b78955728bffa7efa54297c6a5d73337bd6280205b1759c13\
    \f79d4c93f29871fc51b78aeba80e58200000000000000000000000\
    \00000000000000000000000000000000000000000044a1024100f5\
    \f6"

babbageTx :: Tx Babbage
babbageTx = unsafeParseEraTxFromHex
    "84a400818258200000000000000000000000000000000000000000\
    \000000000000000000000000000182a20058390101010101010101\
    \010101010101010101010101010101010101010101010101010101\
    \01010101010101010101010101010101010101010101011a001e84\
    \80a200583901020202020202020202020202020202020202020202\
    \020202020202020202020202020202020202020202020202020202\
    \0202020202020202011a0078175c021a0001faa403191e46a10281\
    \845820010000000000000000000000000000000000000000000000\
    \000000000000000058407154db81463825f150bb3b9b0824caf151\
    \3716f73498afe61d917a5621912a2b3df252bea14683a9ee56710d\
    \483a53a5aa35247e0d2b80e6300f7bdec763a20458200000000000\
    \000000000000000000000000000000000000000000000000000000\
    \44a1024100f5f6"

conwayTx :: Tx Conway
conwayTx = unsafeParseEraTxFromHex
    "84A5008182582000000000000000000000000000000000000000000000000000\
    \00000000000000000182A2005839010101010101010101010101010101010101\
    \0101010101010101010101010101010101010101010101010101010101010101\
    \01010101010101011A001E8480A2005839010202020202020202020202020202\
    \0202020202020202020202020202020202020202020202020202020202020202\
    \02020202020202020202011A0078175C021A0001FAA403191E46048183098200\
    \581C0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A0A8200\
    \581C0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0DA102\
    \8184582001000000000000000000000000000000000000000000000000000000\
    \0000000058407154DB81463825F150BB3B9B0824CAF1513716F73498AFE61D91\
    \7A5621912A2B3DF252BEA14683A9EE56710D483A53A5AA35247E0D2B80E6300F\
    \7BDEC763A2045820000000000000000000000000000000000000000000000000\
    \000000000000000044A1024100F5F6"

-- | Parse a hex-encoded transaction into a particular era.
unsafeParseEraTxFromHex :: forall era. IsEra era => ByteString -> Tx era
unsafeParseEraTxFromHex bytes =
    either (error . show) id
    $ deserializeTx (unsafeReadBase16 bytes :: BL.ByteString)

unsafeReadBase16 :: ByteString -> BL.ByteString
unsafeReadBase16 = either reportError fromStrict . convertFromBase Base16
  where
    reportError = error "unsafeReadBase16: input not in Base16"