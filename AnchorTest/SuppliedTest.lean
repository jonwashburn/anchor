import Anchor
import AnchorTest.Planted

/-!
# Control: a supplied proof of the wrong statement is refused

`dec_01`'s hypothesis 1 is removable, but the declaration supplied under
`dec_01.anchorDrop_1` below proves `True`, not the obligation. Anchor must refuse it and leave
the obligation open with the reason, so the verdict cannot be `DECORATIVE [1]` on its strength.
`scripts/test_planted.sh` checks the printed reason.
-/

anchor_spec AnchorTest.Planted.dec_01

theorem AnchorTest.Planted.dec_01.anchorDrop_1 : True := trivial

#anchor AnchorTest.Planted.dec_01
