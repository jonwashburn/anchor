import Anchor.SHA256

/-! Standard SHA-256 test vectors (FIPS 180-4 examples and the empty string), checked by
evaluation when this file is compiled. A wrong round constant fails every line. -/

open Anchor.SHA256

/-- Fail the build unless `ofString s = expected`. -/
def expect (s expected : String) : IO Unit := do
  let got := ofString s
  unless got == expected do
    throw <| IO.userError s!"sha256 {s.quote}: got {got}, expected {expected}"
  IO.println s!"ok {got}"

#eval expect "" "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#eval expect "abc" "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#eval expect "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#eval expect ("a".pushn 'a' 999)
  "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
