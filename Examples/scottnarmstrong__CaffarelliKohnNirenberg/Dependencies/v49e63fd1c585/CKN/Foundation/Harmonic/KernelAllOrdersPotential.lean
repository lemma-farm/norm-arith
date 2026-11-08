-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersShift
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersOpen
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Bounds
set_option autoImplicit false
set_option warningAsError true
universe u
open scoped BigOperators Topology
open MeasureTheory
open CKN.Foundation.Parabolic
set_option autoImplicit false
/-!
# Potentials of singular kernels away from the support of their density

Let `K` be a kernel that is of every finite differentiability order away from
the origin and whose `j`-th derivative is bounded by `C j ‖z‖₂^{-(m + j)}`, and
let `g` be an integrable density vanishing outside a set `A` separated from an
open set `U` by a distance `δ > 0`.  Then the potential

  `P x = ∫ y, g y • K (x - y)`

is of every finite differentiability order on `U`, its derivative on `U` is the
potential of `fderiv K`, and

  `‖D^k P x‖ ≤ C k δ^{-(m + k)} ‖g‖₁`  for `x ∈ U`.

These are the smooth-off-the-support statements `eq:har-Ck` used by the local
pressure decomposition of `cor:CZ-harmonic`.
-/
noncomputable section
namespace CKN.Foundation.Heat
section KernelData
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Vec3 → F}
end KernelData
/-! ### Smoothness and all-order bounds for the potential -/
section Potential
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Vec3 → F}
  {C : ℕ → ℝ} {m : ℕ} {g : Vec3 → ℝ} {A U : Set Vec3} {δ : ℝ}
end Potential
end CKN.Foundation.Heat
