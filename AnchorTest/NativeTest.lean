import Anchor

/-! A search that closes a goal only through a lemma proved by `native_decide` leaves the
obligation open: the theorem it adds rests on `Lean.ofReduceBool`. Here the conclusion is true
outright and the hypothesis is removable, and Anchor must report neither. -/

@[irreducible] def AnchorTest.Native.g (n : Nat) : Nat := n % 7

@[simp] theorem AnchorTest.Native.g_100 : AnchorTest.Native.g 100 = 2 := by
  unfold AnchorTest.Native.g; native_decide

theorem AnchorTest.Native.t (n : Nat) (_h : 0 < n) : AnchorTest.Native.g 100 = 2 :=
  AnchorTest.Native.g_100

#anchor AnchorTest.Native.t
