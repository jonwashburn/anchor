theorem AnchorTest.Planted.vac_05.anchorVacuous : Anchor.Spec.Vacuous AnchorTest.Planted.vac_05.anchorSpec := by
  delta AnchorTest.Planted.vac_05.anchorSpec
  anchor_unfold
  rintro ⟨s, hs, hc⟩
  have h1 := Finset.card_le_card hs
  rw [Finset.card_range] at h1
  omega
