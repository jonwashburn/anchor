import Anchor
import AnchorTest.Signoff.Fixture

/-!
# What the sign-off machinery and its signed fixture rest on

Compiled after `AnchorTest/Signoff/variants/V0_base.lean.txt` is copied to
`AnchorTest/Signoff/Fixture.lean` and built, as `scripts/test_signoff.sh` does before signing.
-/

#print axioms AnchorTest.Signoff.double_evenish
#print axioms AnchorTest.Signoff.three_pos
#print axioms Anchor.Signoff.canon
#print axioms Anchor.Signoff.surfaceHashes
#print axioms Anchor.Signoff.surfaceHash
#print axioms Anchor.Signoff.sign
#print axioms Anchor.Signoff.check
#print axioms Anchor.SHA256.ofString
