theorem AnchorTest.Planted.dec_07.anchorLoadBearing_0 : Anchor.Spec.LoadBearing AnchorTest.Planted.dec_07.anchorSpec 0 := by
  delta AnchorTest.Planted.dec_07.anchorSpec
  anchor_unfold
  refine ⟨fun _ => (0:ℝ), 0, 1, ⟨continuous_const, rfl⟩, ?_, ?_⟩
  · intro h
    have := h (show (0:ℝ) < 1 by norm_num)
    exact lt_irrefl _ this
  · norm_num
