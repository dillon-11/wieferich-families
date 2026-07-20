import Lake
open Lake DSL

package wieferichFamilies where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0-rc1"

lean_lib Challenge where
  globs := #[.one `Challenge]

/-- The Lean companion of "Wieferich phenomena of algebraic units": the
census mechanism layer (order-lift dichotomy, higher-depth algebra,
empty-class classification, Zsygmondy/LTE scaffold, Dobrowolski
depth-grading, depth transfer) and the construct-and-certify layer
(certified zone, Aurifeuillian seams, search-cost model). -/
@[default_target]
lean_lib WieferichFamilies where
  globs := #[.andSubmodules `WieferichFamilies]
