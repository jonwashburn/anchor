import Lake
open Lake DSL

package anchor where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

/-- The certificate notions and the machinery that extracts, checks and reports them. -/
@[default_target]
lean_lib Anchor where

/-- The planted suite, the tests, the findings and the Mathlib census driver. -/
lean_lib AnchorTest where

/-- `lake exe anchor check`: list sign-offs whose review surface changed. -/
lean_exe anchor where
  root := `Anchor.Main
  supportInterpreter := true
