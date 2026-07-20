import Lake
open Lake DSL

package wieferichFamilies where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0-rc1"

/-- The Lean companion of "Wieferich phenomena of algebraic units": the
census mechanism layer (order-lift dichotomy, super-Wieferich
algebra, empty-class classification, Zsygmondy/LTE scaffold, Dobrowolski depth-grading,
weave depth) and the construct-and-certify layer (certified zone,
Aurifeuillian seams, end-to-end engine cost). -/
@[default_target]
lean_lib WieferichFamilies where
  globs := #[.andSubmodules `WieferichFamilies]
