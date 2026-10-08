theorem AnchorTest.Planted.dec_08.anchorDrop_0 : Anchor.Spec.Drop AnchorTest.Planted.dec_08.anchorSpec 0 := by
  delta AnchorTest.Planted.dec_08.anchorSpec
  anchor_unfold
  intro G inst a b h
  rw [mul_eq_one_iff_eq_inv] at h
  rw [h]
  exact mul_inv_cancel b
