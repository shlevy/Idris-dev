module Data.Buffer

%default total

-- !!! TODO: Open issues:
-- 1. It may be theoretically nice to represent Buffer size as
--    Fin (2 ^ WORD_BITS) instead of Nat
-- 2. Primitives take Bits64 when really they should take the
--    equivalent of C's size_t (ideally unboxed)
-- 3. If we had access to host system information, we could have
--    "native" variants of the multibyte peeks and appends for use
--    cases where we know we don't care about endianness
-- 4. Would be nice to be able to peek/append Int, Char, and Float,
--    all have fixed (though possibly implementation-dependent) widths.
--    Currently not in place due to lack of host system introspection.
-- 5. Would be nice to be able to peek/append the vector types, but
--    for now I'm only touching the C backend which AFAICT doesn't
--    support them.
-- 6. Conversion from Fin to Bits64 (which, re 2, should eventually
--    be a fixed-width implementation-dependent type) is likely
--    inefficient relative to conversion from Nat to Bits64
-- 7. We may want to have a separate type that is a product of Buffer
--    and offset rather than storing the offset in Buffer itself

-- A contiguous chunk of n bytes
abstract
record Buffer : Nat -> Type where
  MkBuffer : ( offset : Nat ) -> ( realBuffer : prim__UnsafeBuffer ) -> Buffer n

-- Make a view over a Buffer
public
peekBuffer : Buffer ( m + n ) -> ( offset : Fin ( S n ) ) -> Buffer m
peekBuffer ( MkBuffer o r ) = flip MkBuffer r . plus o . finToNat

bitsFromNat : Nat -> Bits64
bitsFromNat Z     = 0
bitsFromNat (S k) = 1 + bitsFromNat k

-- Allocate an empty Buffer. The size hint can be used to avoid
-- unnecessary reallocations and copies under the hood if the
-- approximate ultimate size of the Buffer is known. Users can assume
-- the new Buffer is word-aligned.
public
allocate : ( hint : Nat ) -> Buffer Z
allocate = MkBuffer Z . prim__allocate . bitsFromNat

-- Append a Bits8 to a buffer
%assert_total
public
appendBits8 : Buffer n -> Bits8 -> Buffer ( S n )
appendBits8 { n } ( MkBuffer o r ) =
  MkBuffer o . prim__appendBits8 r ( bitsFromNat $ n + o )

-- Read a Bits8 from a buffer at a given offset
%assert_total
public
peekBits8 : Buffer n -> ( offset : Fin n ) -> Bits8
peekBits8 ( MkBuffer o r ) =
  prim__peekBits8 r . bitsFromNat . plus o . finToNat

-- Append a Buffer to another Buffer
public
appendBuffer : Buffer n -> Buffer m -> Buffer ( m + n )
appendBuffer { m=Z } b _ = b
appendBuffer { n } { m=S k } b1 b2 =
  replace ( sym $ plusSuccRightSucc k n ) $ appendBuffer ( appendBits8 b1 $ peekBits8 b2 fZ ) smaller
  where
    smaller : Buffer k
    smaller = peekBuffer { n = S Z } ( replace ( plusCommutative 1 k ) $ replace ( sym $ plusOneSucc k ) b2 ) 1

-- Copy a buffer, potentially allowing the (potentially large) space it
-- pointed to to be freed
public
copy : Buffer n -> Buffer n
copy { n } = replace ( plusZeroRightNeutral n ) . appendBuffer ( allocate n )

-- Read a little-endian Bits16 from a Buffer starting at offset
public
peekBits16LE : Buffer ( S n ) -> ( offset : Fin n ) -> Bits16
peekBits16LE b o = b1 + prim__shlB16 b2 8
  where
    b1 : Bits16
    b1 = prim__zextB8_B16 . peekBits8 b $ weaken o
    b2 : Bits16
    b2 = prim__zextB8_B16 $ peekBits8 b ( fS o )

-- Read a big-endian Bits16 from a Buffer starting at offset
public
peekBits16BE : Buffer ( S n ) -> ( offset : Fin n ) -> Bits16
peekBits16BE b o = b2 + prim__shlB16 b1 8
  where
    b1 : Bits16
    b1 = prim__zextB8_B16 . peekBits8 b $ weaken o
    b2 : Bits16
    b2 = prim__zextB8_B16 $ peekBits8 b ( fS o )

-- Append a little-endian Bits16 to a buffer
public
appendBits16LE : Buffer n -> Bits16 -> Buffer ( S ( S n ) )
appendBits16LE b v = appendBits8 ( appendBits8 b b1 ) b2
  where
    b1 : Bits8
    b1 = prim__truncB16_B8 v
    b2 : Bits8
    b2 = prim__truncB16_B8 $ prim__lshrB16 v 8

-- Append a big-endian Bits16 to a buffer
public
appendBits16BE : Buffer n -> Bits16 -> Buffer ( S ( S n ) )
appendBits16BE b v = appendBits8 ( appendBits8 b b2 ) b1
  where
    b1 : Bits8
    b1 = prim__truncB16_B8 v
    b2 : Bits8
    b2 = prim__truncB16_B8 $ prim__lshrB16 v 8

-- Read a little-endian Bits32 from a Buffer starting at offset
public
peekBits32LE : Buffer ( S ( S ( S n ) ) ) -> ( offset : Fin n ) -> Bits32
peekBits32LE b o = s1 + prim__shlB32 s2 16
  where
    s1 : Bits32
    s1 = prim__zextB16_B32 . peekBits16LE b . weaken $ weaken o
    s2 : Bits32
    s2 = prim__zextB16_B32 $ peekBits16LE b ( fS ( fS o ) )

-- Read a big-endian Bits32 from a Buffer starting at offset
public
peekBits32BE : Buffer ( S ( S ( S n ) ) ) -> ( offset : Fin n ) -> Bits32
peekBits32BE b o = s2 + prim__shlB32 s1 16
  where
    s1 : Bits32
    s1 = prim__zextB16_B32 . peekBits16BE b . weaken $ weaken o
    s2 : Bits32
    s2 = prim__zextB16_B32 $ peekBits16BE b ( fS ( fS o ) )

-- Append a little-endian Bits32 to a buffer
public
appendBits32LE : Buffer n -> Bits32 -> Buffer ( S ( S ( S ( S n ) ) ) )
appendBits32LE b v = appendBits16LE ( appendBits16LE b s1 ) s2
  where
    s1 : Bits16
    s1 = prim__truncB32_B16 v
    s2 : Bits16
    s2 = prim__truncB32_B16 $ prim__lshrB32 v 16

-- Append a big-endian Bits32 to a buffer
public
appendBits32BE : Buffer n -> Bits32 -> Buffer ( S ( S ( S ( S n ) ) ) )
appendBits32BE b v = appendBits16BE ( appendBits16BE b s2 ) s1
  where
    s1 : Bits16
    s1 = prim__truncB32_B16 v
    s2 : Bits16
    s2 = prim__truncB32_B16 $ prim__lshrB32 v 16

-- Read a little-endian Bits64 from a Buffer starting at offset
public
peekBits64LE : Buffer ( S ( S ( S ( S ( S ( S ( S n ) ) ) ) ) ) ) ->
               ( offset : Fin n )                                 ->
               Bits64
peekBits64LE b o = h1 + prim__shlB64 h2 16
  where
    h1 : Bits64
    h1 = prim__zextB32_B64 $ peekBits32LE b . weaken . weaken . weaken $ weaken o
    h2 : Bits64
    h2 = prim__zextB32_B64 $ peekBits32LE b ( fS ( fS ( fS ( fS o ) ) ) )

-- Read a big-endian Bits64 from a Buffer starting at offset
public
peekBits64BE : Buffer ( S ( S ( S ( S ( S ( S ( S n ) ) ) ) ) ) ) ->
               ( offset : Fin n )                                 ->
               Bits64
peekBits64BE b o = h2 + prim__shlB64 h1 16
  where
    h1 : Bits64
    h1 = prim__zextB32_B64 . peekBits32BE b . weaken . weaken . weaken $ weaken o
    h2 : Bits64
    h2 = prim__zextB32_B64 $ peekBits32BE b ( fS ( fS ( fS ( fS o ) ) ) )

-- Append a little-endian Bits64 to a buffer
public
appendBits64LE : Buffer n ->
                 Bits64   ->
                 Buffer ( S ( S ( S ( S ( S ( S ( S ( S n ) ) ) ) ) ) ) )
appendBits64LE b v = appendBits32LE ( appendBits32LE b h1 ) h2
  where
    h1 : Bits32
    h1 = prim__truncB64_B32 v
    h2 : Bits32
    h2 = prim__truncB64_B32 $ prim__lshrB64 v 32

-- Append a big-endian Bits64 to a buffer
public
appendBits64BE : Buffer n ->
                 Bits64   ->
                 Buffer ( S ( S ( S ( S ( S ( S ( S ( S n ) ) ) ) ) ) ) )
appendBits64BE b v = appendBits32BE ( appendBits32BE b h2 ) h1
  where
    h1 : Bits32
    h1 = prim__truncB64_B32 v
    h2 : Bits32
    h2 = prim__truncB64_B32 $ prim__lshrB64 v 32
