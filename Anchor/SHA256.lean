/-
SHA-256 (FIPS 180-4) in plain Lean, so that a sign-off hash needs no external tool.
`AnchorTest/SHA256Test.lean` checks it against the standard test vectors.
-/

namespace Anchor.SHA256

/-- The 64 round constants. -/
def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def h0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotate right by `n` bits, `0 < n < 32`. -/
@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message padded to a multiple of 64 bytes: a one bit, zeros, and the bit length as a
64-bit big-endian number. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut b := msg.push 0x80
  while b.size % 64 != 56 do
    b := b.push 0
  let bits := (len * 8 : Nat)
  for i in [0:8] do
    b := b.push (UInt8.ofNat ((bits >>> (8 * (7 - i))) % 256))
  return b

/-- The big-endian word at byte offset `i`. -/
@[inline] def word (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 <<< 24 ||| (b.get! (i + 1)).toUInt32 <<< 16 |||
    (b.get! (i + 2)).toUInt32 <<< 8 ||| (b.get! (i + 3)).toUInt32

/-- Process one 64-byte block starting at offset `off`. -/
def block (hs : Array UInt32) (b : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    w := w.push (word b (off + 4 * t))
  for t in [16:64] do
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := hs[0]!
  let mut bb := hs[1]!
  let mut c := hs[2]!
  let mut d := hs[3]!
  let mut e := hs[4]!
  let mut f := hs[5]!
  let mut g := hs[6]!
  let mut h := hs[7]!
  for t in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := h + S1 + ch + k[t]! + w[t]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& bb) ^^^ (a &&& c) ^^^ (bb &&& c)
    let t2 := S0 + maj
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := bb
    bb := a
    a := t1 + t2
  return #[hs[0]! + a, hs[1]! + bb, hs[2]! + c, hs[3]! + d, hs[4]! + e, hs[5]! + f,
    hs[6]! + g, hs[7]! + h]

/-- Two lowercase hexadecimal digits. -/
def hexByte (x : Nat) : String :=
  let d (n : Nat) : Char := "0123456789abcdef".toList[n]!
  String.ofList [d (x / 16 % 16), d (x % 16)]

/-- The SHA-256 digest of a byte array, as 64 lowercase hexadecimal digits. -/
def ofBytes (msg : ByteArray) : String := Id.run do
  let b := pad msg
  let mut hs := h0
  for i in [0:b.size / 64] do
    hs := block hs b (64 * i)
  let mut out := ""
  for x in hs do
    for j in [0:4] do
      out := out ++ hexByte ((x >>> (8 * (3 - j).toUInt32)).toNat % 256)
  return out

/-- The SHA-256 digest of a string's UTF-8 bytes. -/
def ofString (s : String) : String := ofBytes s.toUTF8

end Anchor.SHA256
