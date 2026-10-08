theorem AnchorTest.Planted.vac_10.anchorVacuous : Anchor.Spec.Vacuous AnchorTest.Planted.vac_10.anchorSpec := by
  delta AnchorTest.Planted.vac_10.anchorSpec
  anchor_unfold
  rintro ⟨l, hl, hs, hx⟩
  match l, hl, hs, hx with
  | [x, y], _, hs, hx =>
    have h1 := hx x (by simp)
    have h2 := hx y (by simp)
    simp at hs
    omega
