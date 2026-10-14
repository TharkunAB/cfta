{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

{- | Memo tables keyed by three integers.

A 'FlatTable' is an open-addressing hash table. It keeps its keys unboxed in
one byte array and its values in one boxed array. A lookup reads the keys of
one slot, and usually of the next slots in the same cache line, and then one
value. A hash map of boxed keys reads one node at each level of its trie, and
then the key.

Slot @i@ keeps its three keys at words @3i@, @3i + 1@, and @3i + 2@ of the key
array, and its value at element @i@ of the value array. The first key of an
empty slot is -1, so every first key must be non-negative. The identities
from an 'Data.CFTA.Interned.Cache.IdSupply' start at 0, so they obey this
rule.

The hash multiplies each key by a different odd constant, adds the products,
and mixes the sum with the 64-bit finalizer of MurmurHash3. The capacity is a
power of two, and the low bits of the hash give the first slot. A lookup then
reads the next slots in order (linear probing), until it finds the key or an
empty slot.

The table never evicts. Before an insert makes the table more than half full,
the insert copies all entries to new arrays of double the capacity. Then it
publishes the new arrays. Nothing writes the old arrays again.

Safe from any thread. A lookup takes no lock. An insert takes the lock of the
table, an 'MVar' that also holds the number of entries. Under the lock, the
insert looks for the key again, so the first stored value wins. The insert
writes the value and the second and third keys first. Then it writes the
first key with an atomic write. A lookup reads the first key with an atomic
read. Thus a lookup that sees the first key of a slot also sees the other keys
and the value. A lookup that does not find a key goes to the insert, and the
insert finds the key if another thread stored it.

The insert calls 'noDuplicate' before it takes the lock. A memoized function
runs in 'unsafeDupablePerformIO'. When two threads evaluate one thunk, the
runtime can stop one of them at any point, and that thread does not continue.
A thread that stops while it holds the lock blocks all inserts after it.
After 'noDuplicate', this thread alone evaluates the thunks on its stack, so
the runtime does not stop it. With one capability, 'noDuplicate' does nothing.

The table does not force a value. To force a value can call the memoized
function again, and that call can insert into this table.
-}
module Data.CFTA.Interned.FlatMemo (
    FlatTable,
    newFlatTable,
    lookupOrInsert,
    FlatMemoCache,
    newFlatMemoCache,
    memoFlatTypeableWith,
) where

import Control.Concurrent.MVar (MVar, modifyMVarMasked, newMVar)
import Data.Bits (shiftR, xor, (.&.))
import Data.IORef (IORef, atomicWriteIORef, newIORef, readIORef)
import GHC.Exts (
    Int (I#),
    MutableArray#,
    MutableByteArray#,
    RealWorld,
    atomicReadIntArray#,
    atomicWriteIntArray#,
    newArray#,
    newByteArray#,
    readArray#,
    readIntArray#,
    setByteArray#,
    writeArray#,
    writeIntArray#,
 )
import GHC.IO (IO (IO), unsafeDupablePerformIO)
import GHC.IO.Unsafe (noDuplicate)
import Type.Reflection (Typeable)

import Data.CFTA.Interned.Cache (CacheFamily, newCacheFamily, selectCache)

-- | A memo table keyed by three integers. The first integer is non-negative.
data FlatTable value
    = FlatTable
        -- | The lock for inserts. It holds the number of entries.
        !(MVar Int)
        -- | The arrays that the table uses now.
        !(IORef (Slots value))

-- | The arrays of a table at one capacity.
data Slots value
    = Slots
        -- | The capacity minus one. The capacity is a power of two.
        !Int
        -- | The keys, three words for each slot.
        (MutableByteArray# RealWorld)
        -- | The values, one element for each slot.
        (MutableArray# RealWorld value)

-- | The number of slots in a new table.
initialCapacity :: Int
initialCapacity = 1024

-- | Allocate an empty table.
newFlatTable :: IO (FlatTable value)
newFlatTable = FlatTable <$> newMVar 0 <*> (newSlots initialCapacity >>= newIORef)

-- | Allocate empty arrays for a power-of-two number of slots.
newSlots :: Int -> IO (Slots value)
newSlots capacity@(I# slots) = IO $ \s0 -> case newByteArray# bytes s0 of
    (# s1, keys #) -> case setByteArray# keys 0# bytes 255# s1 of
        s2 -> case newArray# slots emptyValue s2 of
            (# s3, values #) -> (# s3, Slots (capacity - 1) keys values #)
  where
    !(I# bytes) = 24 * capacity

-- | The value of an empty slot. Nothing reads it.
emptyValue :: value
emptyValue = error "FlatTable: the value of an empty slot"

-- | The first slot to read for a key.
firstSlot :: Int -> Int -> Int -> Int -> Int
{-# INLINE firstSlot #-}
firstSlot mask a b c = fromIntegral (finalize sum3) .&. mask
  where
    sum3 :: Word
    sum3 = fromIntegral a * 0x9e3779b97f4a7c15 + fromIntegral b * 0xc2b2ae3d27d4eb4f + fromIntegral c
    finalize :: Word -> Word
    finalize h0 =
        let h1 = (h0 `xor` (h0 `shiftR` 33)) * 0xff51afd7ed558ccd
            h2 = (h1 `xor` (h1 `shiftR` 33)) * 0xc4ceb9fe1a85ec53
         in h2 `xor` (h2 `shiftR` 33)

{- | Find a key. Give its slot when the arrays hold it. Otherwise give minus
one minus the empty slot where the search stops.
-}
findSlot :: Slots value -> Int -> Int -> Int -> IO Int
{-# INLINE findSlot #-}
findSlot (Slots mask keys _) a b c = go (firstSlot mask a b c)
  where
    go i = do
        first <- atomicReadKey keys (3 * i)
        if
            | first == -1 -> pure (-1 - i)
            | first == a -> do
                second <- readKey keys (3 * i + 1)
                third <- readKey keys (3 * i + 2)
                if second == b && third == c then pure i else go ((i + 1) .&. mask)
            | otherwise -> go ((i + 1) .&. mask)

{- | Give the value of a key. When the table does not hold the key, store the
given value for it, and give that value. The value stays unevaluated.
-}
lookupOrInsert :: FlatTable value -> Int -> Int -> Int -> value -> IO value
{-# INLINE lookupOrInsert #-}
lookupOrInsert table@(FlatTable _ current) !a !b !c value = do
    slots <- readIORef current
    i <- findSlot slots a b c
    if i >= 0 then readValue slots i else insert table a b c value

-- | Store a value for a key under the lock, unless the table holds the key.
insert :: FlatTable value -> Int -> Int -> Int -> value -> IO value
{-# NOINLINE insert #-}
insert (FlatTable lock current) a b c value = do
    noDuplicate
    modifyMVarMasked lock $ \count -> do
        slots@(Slots mask _ _) <- readIORef current
        i <- findSlot slots a b c
        if
            | i >= 0 -> (count,) <$> readValue slots i
            | 2 * (count + 1) > mask + 1 -> do
                grown <- grow slots
                atomicWriteIORef current grown
                j <- findSlot grown a b c
                write grown (-1 - j) a b c value
                pure (count + 1, value)
            | otherwise -> do
                write slots (-1 - i) a b c value
                pure (count + 1, value)

-- | Copy all entries to new arrays of double the capacity.
grow :: Slots value -> IO (Slots value)
grow old@(Slots mask keys _) = do
    new <- newSlots (2 * (mask + 1))
    let copy i
            | i > mask = pure new
            | otherwise = do
                first <- readKey keys (3 * i)
                if first == -1
                    then copy (i + 1)
                    else do
                        second <- readKey keys (3 * i + 1)
                        third <- readKey keys (3 * i + 2)
                        value <- readValue old i
                        j <- findSlot new first second third
                        write new (-1 - j) first second third value
                        copy (i + 1)
    copy 0

-- | Fill an empty slot. Write the first key last.
write :: Slots value -> Int -> Int -> Int -> Int -> value -> IO ()
write (Slots _ keys values) i a b c value = do
    writeValue values i value
    writeKey keys (3 * i + 1) b
    writeKey keys (3 * i + 2) c
    atomicWriteKey keys (3 * i) a

-- | Read one word of the keys.
readKey :: MutableByteArray# RealWorld -> Int -> IO Int
{-# INLINE readKey #-}
readKey keys (I# i) = IO $ \s -> case readIntArray# keys i s of
    (# s', k #) -> (# s', I# k #)

-- | Read one word of the keys with an atomic read.
atomicReadKey :: MutableByteArray# RealWorld -> Int -> IO Int
{-# INLINE atomicReadKey #-}
atomicReadKey keys (I# i) = IO $ \s -> case atomicReadIntArray# keys i s of
    (# s', k #) -> (# s', I# k #)

-- | Write one word of the keys.
writeKey :: MutableByteArray# RealWorld -> Int -> Int -> IO ()
{-# INLINE writeKey #-}
writeKey keys (I# i) (I# k) = IO $ \s -> (# writeIntArray# keys i k s, () #)

-- | Write one word of the keys with an atomic write.
atomicWriteKey :: MutableByteArray# RealWorld -> Int -> Int -> IO ()
{-# INLINE atomicWriteKey #-}
atomicWriteKey keys (I# i) (I# k) = IO $ \s -> (# atomicWriteIntArray# keys i k s, () #)

-- | Read the value of a slot, without forcing it.
readValue :: Slots value -> Int -> IO value
{-# INLINE readValue #-}
readValue (Slots _ _ values) (I# i) = IO $ \s -> readArray# values i s

-- | Write the value of a slot, without forcing it.
writeValue :: MutableArray# RealWorld value -> Int -> value -> IO ()
{-# INLINE writeValue #-}
writeValue values (I# i) value = IO $ \s -> (# writeArray# values i value s, () #)

{- | A family of flat memo tables for one function.

Each symbol type has its own table, and the symbol type must determine the
type of the results.
-}
newtype FlatMemoCache = FlatMemoCache CacheFamily

-- | Allocate an empty family.
newFlatMemoCache :: IO FlatMemoCache
newFlatMemoCache = FlatMemoCache <$> newCacheFamily

{- | Memoize one application in the table for the symbol type. The three
integers are the key, and the last argument is the result for that key.
-}
memoFlatTypeableWith ::
    forall symbol value.
    (Typeable symbol) =>
    FlatMemoCache ->
    Int ->
    Int ->
    Int ->
    value ->
    value
{-# INLINE memoFlatTypeableWith #-}
memoFlatTypeableWith (FlatMemoCache family) a b c value =
    unsafeDupablePerformIO (lookupOrInsert (selectCache @symbol family newFlatTable) a b c value)
