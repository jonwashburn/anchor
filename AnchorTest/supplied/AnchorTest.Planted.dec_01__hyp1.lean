theorem AnchorTest.Planted.dec_01.anchorDrop_1 : Anchor.Spec.Drop AnchorTest.Planted.dec_01.anchorSpec 1 := by
  delta AnchorTest.Planted.dec_01.anchorSpec
  anchor_unfold
  intro K inst a b h
  have hb : b ≠ 0 := by
    rintro rfl
    rw [div_zero] at h
    exact zero_ne_one h
  exact (div_eq_one_iff_eq hb).mp h
