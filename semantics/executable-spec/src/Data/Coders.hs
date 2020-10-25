{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators  #-}

{-# OPTIONS_GHC  -fno-warn-orphans #-}

-- | MemoBytes is an abstration for a datetype that encodes its own seriialization.
--   The idea is to use a newtype around a MemoBytes non-memoizing version.
--   For example:   newtype Foo = Foo(MemoBytes NonMemoizingFoo)
--   This way all the instances for Foo (Eq,Show,Ord,ToCBOR,FromCBOR,NoThunks,Generic)
--   can be derived for free.
module Data.Coders
  ( Encode (..),
    Decode (..),
    (!>),
    (<!),
    Wrapped (..),
    encode,
    decode,
    runE,            -- Used in testing
    decodeClosed,    -- Used in testing
    decodeList,
    decodeSeq,
    decodeStrictSeq,
    decodeSet,
    encodeList,
    encodeSeq,
    encodeStrictSeq,
    encodeSet,
    decodeRecordNamed,
    decodeRecordSum,
    invalidKey,
    wrapCBORArray,
    encodeFoldable,
    decodeCollectionWithLen,
    decodeCollection,
    encodeFoldableEncoder,
    roundTrip,
    roundTrip',
    foo,foo',defaultA,bar,bar', makeDecoder,baz,boxA,decodeA,
    ok,
  )
where

import Data.Array
import Cardano.Prelude (cborError)
import Control.Monad (replicateM,unless)
import Codec.CBOR.Decoding (Decoder)
import Codec.CBOR.Encoding (Encoding)
import Codec.CBOR.Read(DeserialiseFailure,deserialiseFromBytes)
import Codec.CBOR.Write (toLazyByteString)
import qualified Data.ByteString.Lazy as Lazy
import Cardano.Binary
  ( FromCBOR (fromCBOR),
    ToCBOR (toCBOR),
    encodeListLen,
    encodeWord,
    encodeBreak,
    encodeListLenIndef,
    DecoderError( DecoderErrorCustom ),
    decodeBreakOr,
    decodeListLenOrIndef,
    decodeWord,
    matchSize,
  )
import qualified Data.Sequence as Seq
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Sequence.Strict (StrictSeq)
import Data.Sequence (Seq)
import Data.Set (Set,isSubsetOf,insert,member)
import Data.Text (Text,pack)
import Data.Foldable (foldl')
import Data.Typeable

-- ====================================================================

decodeRecordNamed :: Text -> (a -> Int) -> Decoder s a -> Decoder s a
decodeRecordNamed name getRecordSize decoder = do
  lenOrIndef <- decodeListLenOrIndef
  x <- decoder
  case lenOrIndef of
    Just n -> matchSize (Text.pack "\nRecord " <> name) n (getRecordSize x)
    Nothing -> do
      isBreak <- decodeBreakOr
      unless isBreak $ cborError $ DecoderErrorCustom name "Excess terms in array"
  pure x

decodeRecordSum :: String -> (Word -> Decoder s (Int, a)) -> Decoder s a
decodeRecordSum name decoder = do
  lenOrIndef <- decodeListLenOrIndef
  tag <- decodeWord
  (size, x) <- decoder tag -- we decode all the stuff we want
  case lenOrIndef of
    Just n -> matchSize (Text.pack ("\nSum " ++ name ++ "\nreturned=" ++ show size ++ " actually read= " ++ show n)) size n
    Nothing -> do
      isBreak <- decodeBreakOr -- if there is stuff left, it is unnecessary extra stuff
      unless isBreak $ cborError $ DecoderErrorCustom (Text.pack name) "Excess terms in array"
  pure x

invalidKey :: Word -> Decoder s a
invalidKey k = cborError $ DecoderErrorCustom "not a valid key:" (Text.pack $ show k)

decodeList :: Decoder s a -> Decoder s [a]
decodeList = decodeCollection decodeListLenOrIndef

decodeSeq :: Decoder s a -> Decoder s (Seq a)
decodeSeq decoder = Seq.fromList <$> decodeList decoder

decodeStrictSeq :: Decoder s a -> Decoder s (StrictSeq a)
decodeStrictSeq decoder = StrictSeq.fromList <$> decodeList decoder

decodeSet :: Ord a => Decoder s a -> Decoder s (Set a)
decodeSet decoder = Set.fromList <$> decodeList decoder

decodeCollection :: Decoder s (Maybe Int) -> Decoder s a -> Decoder s [a]
decodeCollection lenOrIndef el = snd <$> decodeCollectionWithLen lenOrIndef el

decodeCollectionWithLen ::
  Decoder s (Maybe Int) ->
  Decoder s a ->
  Decoder s (Int, [a])
decodeCollectionWithLen lenOrIndef el = do
  lenOrIndef >>= \case
    Just len -> (,) len <$> replicateM len el
    Nothing -> loop (0, []) (not <$> decodeBreakOr) el
  where
    loop (n, acc) condition action =
      condition >>= \case
        False -> pure (n, reverse acc)
        True -> action >>= \v -> loop (n + 1, (v : acc)) condition action

encodeFoldable :: (ToCBOR a, Foldable f) => f a -> Encoding
encodeFoldable = encodeFoldableEncoder toCBOR

encodeFoldableEncoder :: (Foldable f) => (a -> Encoding) -> f a -> Encoding
encodeFoldableEncoder encoder xs = wrapCBORArray len contents
  where
    (len, contents) = foldl' go (0, mempty) xs
    go (!l, !enc) next = (l + 1, enc <> encoder next)

wrapCBORArray :: Word -> Encoding -> Encoding
wrapCBORArray len contents =
  if len <= 23
    then encodeListLen len <> contents
    else encodeListLenIndef <> contents <> encodeBreak


-- ===============================================================================
-- Encode and Decode are typed data structures which specify encoders and decoders.
-- They keep one from making mistakes by exploting types, and counting the correct number fields
-- in an encoding and decoding. They are somewhat dual, and are designed that visual
-- inspection of a Encode and its dual Decode can help the user conclude that the
-- two are self-consistent. They are also reusable abstractions that can be defined
-- once, and then used many places.
--
-- (Encode t) is a data structure from which 3 things can be recovered
-- Given:    x :: Encode t
-- 1) get a value of type t
-- 2) get an Encoding for that value, which correctly encodes the number of "fields"
--    written to the ByteString. Care must still be taken that the tags are correct.
-- 3) get a (MemoBytes t)
-- The advantage of using Encode with a MemoBytes, is we don't have to make a ToCBOR
-- instance. Instead the "instance" is spread amongst the pattern constuctors by using
-- (memoBytes encoding) in the where clause of the pattern contructor.
-- See some examples of this see the file Timelocks.hs
--
-- The Encode and Decode mechanism can also be used to encode Algebraic datatypes
-- in a uniform way. (Decode t) is dual to (Encode t). A decoder can be extracted
-- from it. And it will consistently decode it's dual. We now give some examples.
-- In the examples Let  Int and C have ToCBOR instances, and
-- encodeB :: B -> Encoding, and decodeB :: Decoder s B
{-
-- An example with 1 constructor (a record) uses Rec and RecD

data A = ACon Int B C

encodeA :: A -> Encode 'Closed A
encodeA (ACon i b c) = Rec ACon !> To i !> E encodeB b !> To c

decodeA :: Decode 'Closed A
decodeA = RecD ACon <! From <! D decodeB <! From

instance ToCBOR A   where toCBOR x = encode(encodeA x)
instance FromCBOR A where fromCBOR = decode decodeA

-- An example with multiple constructors uses Sum, SumD, and Summands

data M = M1 Int | M2 B Bool | M3 A

encodeM :: M -> Encode 'Open M
encodeM (M1 i)    = Sum M1 0 !> To i
encodeM (M2 b tf) = Sum M2 1 !> E encodeB b  !> To tf
encodeM (M3 a)    = Sum M3 2 !> To a

decodeM :: Decode 'Closed M
decodeM = Summands "M" decodeMx
  where decodeMx 0 = SumD M1 <! From
        decodeMx 1 = SumD M2 <! D decodeB <! From
        decodeMx 3 = SumD M3 <! From
        decodeMx k = Invalid k

instance ToCBOR M   where toCBOR x = encode(encodeM x)
instance FromCBOR M where fromCBOR = decode decodeM
-}
-- For more examples writing CBOR instances using Encode and Decode see the test file
-- shelley-spec-ledger-test/test/Test/Shelley/Spec/Ledger/MemoBytes.hs

-- ========================================================

-- | Some CBOR instances wrap encoding sequences with prefixes and suffixes. I.e.
--  prefix , encode, encode, encode , ... , suffix
--  A type that MUST do this is called 'Open. Other types are called 'Closed.
--  The point is that a Closed type may have a prefix, but it can still be 'inlined'
--  by using the context it appears in, inside another Closed type. It does so by
--  sharing the prefix of its containing type, and using positional context.
--  In terms of Open and Closed, a datatype with more than one constructor is Open,
--  and one with only one constructor is Closed (we call these records). Primitive
--  types with no constructors can also be inlined, so we mark them as closed.
data Wrapped = Open | Closed
  deriving Typeable

-- ===========================================================

data Encode (w :: Wrapped) t where
  Sum :: t -> Word -> Encode 'Open t
  Rec :: t -> Encode 'Closed t
  To :: (FromCBOR a,ToCBOR a) => a -> Encode 'Closed a
  E :: (t -> Encoding) -> t -> Encode 'Closed t
  ApplyE ::(Typeable a, Show a) => Encode w (a -> t) -> Encode 'Closed a -> Encode w t
  OmitC :: (Eq t,FromCBOR t) => t -> Encode 'Closed t
  Omit:: (t -> Bool) -> Encode 'Closed t -> Encode 'Closed t
  Tag :: Word -> Encode 'Closed t -> Encode 'Closed t

-- The Wrapped index of ApplyE is determined by the index
-- at the bottom of its left spine. The LEFT arg of ApplyE
-- must be a function type, and the only Encode with function
-- types are (Sum c tag) and (Rec c). So if the leftmost spine
-- is (Sum c tag) it is 'Open, and if is (Rec c) it is 'Closed.
-- The RIGHT arg of ApplyE must be 'Closed. This allows us to
-- inline anything in a RIGHT arg, supporting CBORGroup capability.

infixl 4 !>

(!>) :: (Typeable a,Show a) => Encode w (a -> t) -> Encode 'Closed a -> Encode w t
x !> y = ApplyE x y

runE :: Encode w t -> t
runE (Sum cn _) = cn
runE (Rec cn) = cn
runE (ApplyE f x) = runE f (runE x)
runE (To x) = x
runE (E _ x) = x
runE (OmitC x) = x
runE (Omit _ x) = runE x
runE (Tag _ x) = runE x

gsize :: Encode w t -> Word
gsize (Sum _ _) = 0
gsize (Rec _) = 0
gsize (To _) = 1
gsize (E _ _) = 1
gsize (ApplyE f x) = gsize f + gsize x
gsize (OmitC _) = 0
gsize (Omit p x) = if p (runE x) then 0 else gsize x
gsize (Tag _ x) = gsize x

encode :: Encode w t -> Encoding
encode sym = encodeCountPrefix 0 sym
  where
    encodeCountPrefix :: Word -> Encode w t -> Encoding
    encodeCountPrefix n (Sum _ tag) = encodeListLen (n + 1) <> encodeWord tag
    encodeCountPrefix n (Rec _) = encodeListLen n
    -- n is the number of fields we must write in the prefx.
    encodeCountPrefix _ (To x) = toCBOR x
    encodeCountPrefix _ (E enc x) = enc x
    encodeCountPrefix n (ApplyE f x) =
      encodeCountPrefix (n + gsize x) f <> encodeClosed x
    -- The RIGHT arg may be any 'Closed Encode, and is inlined
    -- by design. Its left spine must end in a (Rec c). We count (gsize x)
    -- the 'fields' in x, and add them to the number things we
    -- must add to the prefix of the enclosing type.
    encodeCountPrefix _ (OmitC _) = mempty
    encodeCountPrefix n (Omit p x) =
       if p (runE x) then mempty else encodeCountPrefix n x
    encodeCountPrefix n (Tag tag x) = encodeWord tag <> encodeCountPrefix n x

    encodeClosed :: Encode 'Closed t -> Encoding
    -- encodeClosed (Sum _ _) -- By design this case is unreachable by type considerations.
    encodeClosed (Rec _) = mempty
    encodeClosed (To x) = toCBOR x
    encodeClosed (E enc x) = enc x
    encodeClosed (ApplyE f x) = encodeClosed f <> encodeClosed x
    encodeClosed (OmitC _) = mempty
    encodeClosed (Omit p x) =
       if p (runE x) then mempty else encodeClosed x
    encodeClosed (Tag tag x) = encodeWord tag <> encodeClosed x

-- =====================
data Decode (w :: Wrapped) t where
  Summands :: String -> (Word -> Decode 'Open t) -> Decode 'Closed t
  SumD :: t -> Decode 'Open t
  RecD :: t -> Decode 'Closed t
  From :: FromCBOR t => Decode 'Closed t
  D :: (forall s. Decoder s t) -> Decode 'Closed t
  ApplyD :: (Typeable a,Show a) => Decode w (a -> t) -> Decode 'Closed a -> Decode w t
  Invalid :: Word -> Decode w t
  Map :: (a -> b) -> Decode w a -> Decode w b
  OmitD :: t -> Decode 'Closed t
  UnTag :: Typeable t => t -> (Word -> Box t) -> [Word] -> Decode 'Closed t

infixl 4 <!

(<!) :: (Typeable a,Show a) => Decode w (a -> t) -> Decode 'Closed a -> Decode w t
x <! y = ApplyD x y

hsize :: Decode w t -> Int
hsize (Summands _ _) = 1
hsize (SumD _) = 0
hsize (RecD _) = 0
hsize From = 1
hsize (D _) = 1
hsize (ApplyD f x) = hsize f + hsize x
hsize (Invalid _) = 0
hsize (Map _ x) = hsize x
hsize (OmitD _) = 0
hsize (UnTag _ _ _) = 1

decode :: Decode w t -> Decoder s t
decode x = fmap snd (decodE x)

decodE :: Decode w t -> Decoder s (Int, t)
decodE x = decodeCount x 0

decodeCount :: Decode w t -> Int -> Decoder s (Int, t)
decodeCount (Summands nm f) n = (n + 1,) <$> decodeRecordSum nm (\x -> decodE (f x))
decodeCount (SumD cn) n = pure (n + 1, cn)
decodeCount (RecD cn) n = decodeRecordNamed "RecD" (const n) (pure (n, cn))
decodeCount From n = do x <- fromCBOR; pure (n, x)
decodeCount (D dec) n = do x <- dec; pure (n, x)
decodeCount (ApplyD cn g) n = do
  (i, f) <- decodeCount cn (n + hsize g)
  y <- decodeClosed g
  pure (i, f y)
decodeCount (Invalid k) _ = invalidKey k
decodeCount (Map f x) n = do (m, y) <- decodeCount x n; pure (m, f y)
decodeCount (OmitD x) n = pure(n,x)
decodeCount (u@(UnTag _ _ _)) n = (n+1,) <$> decodeClosed u

decodeClosed :: Decode 'Closed t -> Decoder s t
decodeClosed (Summands nm f) = decodeRecordSum nm (\x -> decodE (f x))
-- decodeClosed (SumD _) = undefined -- This case, by design, is unreachable by type considerations
decodeClosed (RecD cn) = pure cn
decodeClosed From = do x <- fromCBOR; pure x
decodeClosed (D dec) = do x <- dec; pure x
decodeClosed (ApplyD cn g) = do
  f <- decodeClosed cn
  y <- decodeClosed g
  pure (f y)
decodeClosed (Invalid k) = invalidKey k
decodeClosed (Map f x) = f <$> decodeClosed x
decodeClosed (OmitD n) = pure n
decodeClosed (UnTag initial pick required) = do
  lenOrIndef <- decodeListLenOrIndef
  case lenOrIndef of
    Just i -> do (v,used) <- unTagSeries initial pick (Set.empty) i
                 if all (`member` used) required
                    then pure v
                    else unusedKeys used required (show(typeOf initial))
    Nothing -> defaultError "UnTag NOT ListLen encoded"


unusedKeys :: Set Word -> [Word] -> String -> Decoder s a
unusedKeys used required name =
     error ("Required key(s) of type "++name++" with tags "++show unused++" not decoded.")
   where unused = filter (\ x -> not(member x used)) required

defaultError :: String -> Decoder s a
defaultError message = cborError $ DecoderErrorCustom "Default encoding:" (Text.pack $ show message)

instance Functor (Decode w) where
  fmap f (Map g x) = Map (f . g) x
  fmap f x = Map f x

-- | A Box pairs an update function and a decoder for one field of a Record.
data Box t where
  Box:: (x -> t -> t) -> Decode 'Closed x -> Box t

-- | Given a function that picks a Box for a tag, decodes that field
--   and returns a (t -> t) transformer, which when applied, will
--   update the record with the value decoded.

untag :: (Word -> Box t) -> Set Word -> Decoder s (t -> t,Set Word)
untag f seen = do
  tag <- decodeWord
  case f tag of
    Box update d -> do v <- decode d; pure (update v,insert tag seen)

-- | Decode a series (of length n) of tag encoded data for type t
--   given a function that picks the right box for a given tag, and an
--   initial value for the record (usually starts filled with default values).

unTagSeries :: t -> (Word -> Box t) -> Set Word -> Int -> Decoder s (t,Set Word)
unTagSeries t _ seen n | n <= 0 = pure (t, seen)
unTagSeries t pick seen n = do (transform,seen2) <- untag pick seen; unTagSeries (transform t) pick seen2 (n-1)

addtags :: (v -> t -> t) -> Word -> v -> (t,Set Word) -> (t,Set Word)
addtags update tag v (t,tags) = (update v t,insert tag tags)

-- ===========================================================================================
-- These functions are the dual analogs to
-- Shelley.Spec.Ledger.Serialization(decodeList, decodeSeq, decodeStrictSeq, decodeSet)
-- It is not well documented how to use encodeFoldable.
-- They are provided here as compatible pairs for use with the (E x) and (D x) constructors
-- of the Encode and Decode types. (E encodeList xs) and (D (decodeList fromCBOR)) should be duals.

encodeList :: ToCBOR a => [a] -> Encoding
encodeList = encodeFoldable

encodeStrictSeq :: ToCBOR a => StrictSeq a -> Encoding
encodeStrictSeq = encodeFoldable

encodeSeq :: ToCBOR a => Seq a -> Encoding
encodeSeq = encodeFoldable

encodeSet :: ToCBOR a => Set a -> Encoding
encodeSet = encodeFoldable

-- ===========================================
-- For more worked out EXAMPLES see the testfile:
-- cardano-ledger-specs/shelley-ma/impl/test/Test/Cardano/Ledger/ShelleyMA/Timelocks.hs

type Answer t = Either Codec.CBOR.Read.DeserialiseFailure (Lazy.ByteString, t)

roundTrip :: (ToCBOR t,FromCBOR t) => t -> Answer t
roundTrip s = deserialiseFromBytes fromCBOR (toLazyByteString (toCBOR s))

roundTrip' ::(t ->  Encoding) -> (forall s. Decoder s t) -> t -> Answer t
roundTrip' enc dec t = deserialiseFromBytes dec  (toLazyByteString (enc t))

-- ======================================================================
-- There are two ways to write smart encoders and decoders that don't put
-- fields with default values in the Encoding, and that reconstruct them
-- on the decoding side. These techniques work on record datatypes, i.e.
-- those with only one constructor. We will illustrate the two approaches
-- in the datatype A

data A = A Int [Bool] Text
  deriving (Show,Typeable)

-- =======================================================================
-- The first approach makes a virtual constructor (Sum A tag) with one
-- unique tag for each different combination of fields with default values.
-- If there is  1 fields with default values, the number of tags is 2
-- If there are 2 fields with default values, the number of tags is 4
-- If there are 3 fields with default values, the number of tags is 8. etc.
-- We build an Encode for each of the different tag values, Using the Omit or OmitC
-- Encode constructors. These tell what default value to supply if a
-- Encoder is omitted for that field. Here is an exampele for A where there
-- are two fields with default values. 1) The Int. 2) The [Bool]


foo :: A -> (Encode 'Open A)
foo (A 0 [] t) = (Sum A 0 !> OmitC 0 !> OmitC [] !> To t)   -- Both are omitted
foo (A 0 xs t) = (Sum A 1 !> OmitC 0 !> To xs !> To t)      -- Int is omitted
foo (A n [] t) = (Sum A 2 !> To n !> OmitC [] !> To t)      -- [Bool] is omitted
foo (A n xs t) = (Sum A 3 !> To n !> To xs !> To t)         -- Nothing is omitted

smartEncode :: (t -> Encode 'Open t) -> t -> Encoding
smartEncode f x = encode (f x)

-- NOTE THERE IS ONLY ONE TAG, in the entire encoding and decoding
-- encode (foo (A 4 [] (pack "hi"))) -->
--      [TkListLen 3,TkInt 2,TkInt 4,TkString "hi"]
--                         ^tag
-- encode (foo (A 0 [] (pack "hi"))) -->
--      [TkListLen 2,TkInt 0,TkString "hi"]
--                         ^tag
-- encode (foo (A 9 [True] (pack "hi"))) -->
--      [TkListLen 4,TkInt 3,TkInt 9,TkListBegin,TkBool True,TkBreak,TkString "hi"]
--                         ^tag
-- The tag corresponds to which subset of the fileds with default values are present


-- The Dual, is a Decode, that supplies the default value, since we
-- won't try an pull an omitted field off the wire. It is important
-- that the both sides otf the duality agree for each tag, what is omitted,
-- and what the default value for that field is.

bar :: Word -> Decode 'Open A
bar 0 = SumD A <! OmitD 0 <! OmitD [] <! From
bar 1 = SumD A <! OmitD 0 <! From  <! From
bar 2 = SumD A <! From <! OmitD [] <! From
bar 3 = SumD A <! From <! From <! From
bar n = Invalid n

smartDecode :: (Word -> Decode 'Open t) -> Decoder s t
smartDecode f = decodeRecordSum "smart" help
  where help word = decodE (f word)

instance ToCBOR A where
  toCBOR = smartEncode foo

instance FromCBOR A where
  fromCBOR = smartDecode bar

-- ================================================================================
-- The second approach uses N tags, one for each field that is not defaulted
-- encode (baz (A 9 [True] (pack "hi"))) --Here No fields are defaulted, should be 3 tags
-- [TkListLen 3,TkInt 0,TkInt 9,TkInt 1,TkListBegin,TkBool True,TkBreak,TkInt 2,TkString "hi"]
--                    ^tag            ^tag                                    ^tag
-- So the user supplies a function, that encodes every field, each field must use a unique
-- tag, and fields with default values have Omit wrapped around the Tag encoding.
-- The user must ensure that there is NOT an Omit on a required field.

baz:: A -> Encode 'Closed A
baz (A n xs t) = Rec A !> Omit (==0) (Tag 0 (To n)) !> Omit null (Tag 1 (To xs)) !> Tag 2 (To t)

-- To write an Decoder we must pair a decoder for each field, with a function that updates only
-- that field. We use the Box GADT to construct these pairs, and we must write a function, that
-- for each field tag, picks out the correct pair. If the Encode and Decode don't agree on how the
-- tags correspond to a particular field, things will fail.

boxA :: Word -> Box A
boxA 0 = Box update0 From
   where update0 n (A _ xs t) = A n xs t
boxA 1 = Box update1 From
   where update1 xs (A n _ t) = A n xs t
boxA 2 = Box update2 From
   where update2 t (A n xs _) = A n xs t
boxA n = Box (\ _ t -> t) (Invalid n)

-- Finally there is a new constructor for Decode, called UnTag, that decodes field
-- tagged records. The user supplies an intial value and pick function, and a list
-- of tags of therequired fields. The initial value should have default values and
-- any well type value in required fields. If the encode function (baz above) is
-- encoded properly the required fields in the initial value should always be over
-- overwritten. If it is not written properly, or a bad encoding comes from somewhere
-- else, the intial values in the required fields might survive decoding. The list
-- of required fields is checked.

decodeA :: Decode 'Closed A
decodeA = UnTag (A 0 [] (pack "a")) boxA [2]  -- Only the field with Tag 2 is required

-- ===============================================================================
-- We can generate things like foo and bar in the first approach using 1 liners
-- First we write a one line Encode that uses Omit with predicates, rather than OmitC.
-- wrapped around every field with default values. This tells us 3 things
-- 1) Which fields can be omitted
-- 2) How to test if a value should be omitted
-- 3) The value to supply if they are omitted
-- This is a much more compact way of writing foo, where we don't have to enumerate all
-- 2^k different patterns of what should be defaulted, the prediates do this dynamically.

foo' :: Word -> A -> (Encode 'Open A)
foo' tag (A n xs t) = (Sum A tag !> Omit (==0) (To n) !> Omit null (To xs) !> To t)

-- Second we construct a default value. Use the correct defaults in every field
-- specified in foo' above. Non-default fields can have anything with the right type.

defaultA :: A
defaultA = (A 0 [] (pack "ignore_me"))

-- The actual Decode function can be generated by applying the 1 line Encode function
-- (with arbitrary tag) to the default value, and the passing this to makeDecoder.

bar' :: Word -> Decode 'Open A
bar' = makeDecoder (foo' 99 defaultA)

-- ===============================================================
-- The idea is to make a table driven version of bar, given a tag
-- index into a table, and return the result.
-- enumerate the rows of the table in binary counting order
-- So if we have three Omits then the index will count by
-- 0 0 0  index = 0,  all three are omitted
-- 0 0 1  index = 1,  the first two are omitted
-- 0 1 0  index = 2,  the first and third are omitted
-- 0 1 1  etc

makeDecoder :: Encode 'Open t -> (Word -> Decode 'Open t)
makeDecoder sp = \ n -> if (n<0 || n>=m) then Invalid n else table ! n  where
   choices :: Encode w t -> [Decode w t]
   choices (ApplyE f x) = [ApplyD g y | g <- choices f, y <- choices x]
   choices (Omit _ e) =  (OmitD (runE e)) : choices e
   choices (OmitC n) = [OmitD n,From]
   choices (To _) = [From]
   choices (Sum cn _) = [SumD cn]
   choices (Rec cn) = [RecD cn]
   choices (E _ _) = [D $ defaultError "E has no dual"]
   choices (Tag _ _) = [D $ defaultError "Tag has no dual"]

   addTag :: [Decode w t] -> Array Word (Decode w t)
   addTag xs = array (0,n) (label 0 xs)
     where n = fromIntegral (length xs) - 1
           label i (y:ys) = (i,y) : label (i+1) ys
           label _ [] = []
   table = addTag choicelist
   choicelist = (choices sp)
   m = fromIntegral (length choicelist)

-- ====================================================================
-- Some tests

test0,test1,test2,test3,
   test0a,test1a,test2a,test3a,
   test0b,test1b,test2b,test3b,
   test0c,test1c,test2c,test3c :: Answer A

test0 = roundTrip' (smartEncode foo) (smartDecode bar) (A 0 [] (pack "a"))
test1 = roundTrip' (smartEncode foo) (smartDecode bar) (A 0 [True] (pack "a"))
test2 = roundTrip' (smartEncode foo) (smartDecode bar) (A 9 [] (pack "a"))
test3 = roundTrip' (smartEncode foo) (smartDecode bar) (A 9 [True] (pack "a"))

test0a = roundTrip' (smartEncode $ foo' 0) (smartDecode bar) (A 0 [] (pack "a"))
test1a = roundTrip' (smartEncode $ foo' 1) (smartDecode bar) (A 0 [True] (pack "a"))
test2a = roundTrip' (smartEncode $ foo' 2) (smartDecode bar) (A 9 [] (pack "a"))
test3a = roundTrip' (smartEncode $ foo' 3) (smartDecode bar) (A 9 [True] (pack "a"))

test0b = roundTrip' (smartEncode foo) (smartDecode bar') (A 0 [] (pack "b"))
test1b = roundTrip' (smartEncode foo) (smartDecode bar') (A 0 [True] (pack "b"))
test2b = roundTrip' (smartEncode foo) (smartDecode bar') (A 9 [] (pack "b"))
test3b = roundTrip' (smartEncode foo) (smartDecode bar') (A 9 [True] (pack "b"))

test0c = roundTrip' (smartEncode $ foo' 0) (smartDecode bar') (A 0 [] (pack "c"))
test1c = roundTrip' (smartEncode $ foo' 1) (smartDecode bar') (A 0 [True] (pack "c"))
test2c = roundTrip' (smartEncode $ foo' 2) (smartDecode bar') (A 9 [] (pack "c"))
test3c = roundTrip' (smartEncode $ foo' 3) (smartDecode bar') (A 9 [True] (pack "c"))

q0,q1,q2,q3 :: Answer A
q0 = roundTrip' (\ x -> encode(baz x)) (decode decodeA) (A 0 [] (pack "ABC"))
q1 = roundTrip' (\ x -> encode(baz x)) (decode decodeA) (A 0 [True] (pack "ABC"))
q2 = roundTrip' (\ x -> encode(baz x)) (decode decodeA) (A 42 [] (pack "ABC"))
q3 = roundTrip' (\ x -> encode(baz x)) (decode decodeA) (A 9 [True,False] (pack "ABC"))


ok:: Bool
ok = all isRight [ test0,  test1,  test2,  test3
                 , test0a, test1a, test2a, test3a
                 , test0b, test1b, test2b, test3b
                 , test0c, test1c, test2c, test3c
                 , q0, q1, q2, q3 ]
     where isRight (Right _) = True
           isRight (Left _) = False

-- ===================================================================
-- Show instances

instance Show (a -> b) where show _ = "<fun>"

instance Show t => Show (Encode w t) where
  show (Sum _ n) = "Sum "++show n
  show (Rec t) = "Rec "++show t
  show (To t) = "To "++show t
  show (E _ x) = "E "++show x
  show (ApplyE x y) = show x++" !> "++show y
  show (OmitC t) = "OmitC "++show t
  show (Omit _p x) = "Omit ? ("++show x++")"
  show (Tag n x) = "Tag "++show n++"("++show x++")"

instance Show t => Show (Decode w t) where
  show (Summands str _) = "(Summands "++str++")"
  show (SumD t) = "SumD "++show t
  show (RecD t) = "RecD "++show t
  show From = "From"
  show (D _) = "D"
  show (ApplyD x y) = show x++" <! "++show y
  show (Invalid n) = "(Invalid "++show n++")"
  show (Map _f _x) = "Map"
  show (OmitD x) = "OmitD "++show x
  show (UnTag ini _ required) = "(UnTag "++show ini++" "++show required++")"


{- I wonder can you write this function?
import Codec.CBOR.Decoding (Decoder,getDecodeAction,liftST,DecodeAction(Fail))

tryDecoder :: (forall st . Decoder st a)  ->  Decoder s (Maybe a)
tryDecoder d =
   do action <- liftST(getDecodeAction d)
      case action of
          Fail _ -> return Nothing
          _ -> Just <$> d
-}
