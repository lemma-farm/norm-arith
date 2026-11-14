module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0af765ecade9.RegularityStructures.Torus.Basic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The three-torus and space-time

We write `T³ = ℝ³/ℤ³` as `UnitAddTorus (Fin 3)` and space-time `ℝ × T³` as a product. Points of
`ℝ³` are functions `Fin 3 → ℝ`, with the Euclidean square norm written out by hand. A function on
the torus is smooth if its periodic lift to `ℝ³` is smooth.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open scoped ContDiff
namespace RegularityStructures
/-- The three-torus `T³ = ℝ³/ℤ³`. -/
abbrev Torus3 : Type := UnitAddTorus (Fin 3)
/-- Space-time `ℝ × T³`. -/
abbrev SpaceTime : Type := ℝ × Torus3
/-- The projection `ℝ³ → T³`. -/
def torusProj (y : Fin 3 → ℝ) : Torus3 := fun i => ((y i : ℝ) : UnitAddCircle)

/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0af765ecade9.RegularityStructures.Torus.HeatKernel ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Heat kernels on the three-torus

* `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`, the heat kernel on `ℝ³`;
* `heatKernel t`, its periodisation `p_t` on `T³` (the statement, equation (2.1));
* `heatSemigroup s f`, the heat semigroup `P_s` acting on `C(T³)` by convolution with the Gaussian
  on `ℝ³`;
* `massiveHeatKernel`, the kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` of `(∂_t - Δ + 1)⁻¹`
  (equation (2.2)).

The lemmas show that `gaussKernel s` is a probability density for `s > 0`, so `P_s` is linear
and contracts the supremum norm.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open MeasureTheory Real
namespace RegularityStructures
/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) * exp (-sqNorm3 y / (4 * t))

end RegularityStructures
end
/-! ### The Gaussian density on `ℝ³` -/
public section
open MeasureTheory Real
namespace RegularityStructures

/-! ### The heat semigroup -/

/-! ### Values for nonpositive times

The statement defines `γ_t`, `p_t` and `P_t` only for `t > 0`. The Lean functions are total. For
`t ≤ 0` they are zero, because `(4πt)^{-3/2}` is `0` at `t = 0` and is `exp(…) cos(-3π/2) = 0` for
`t < 0`. No result uses these values. -/

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0af765ecade9.RegularityStructures.PDE.HeatOp ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The heat operator on `C(T³, E)`

For a Banach space `E`, `t ∈ ℝ` and `g ∈ C(T³, E)`,
`heatOp t g x = ∫_{ℝ³} γ₁(z) g(x - √t z) dz`, where `γ₁ = gaussKernel 1` is the unit-time heat
kernel on `ℝ³`. For `t > 0` this is the heat semigroup `P_t g(x) = ∫ γ_t(y) g(x - y) dy` after the
substitution `y = √t z`. For `t ≤ 0` the square root vanishes and `heatOp t g = g`.

Writing the operator with the unit Gaussian makes the dependence on `t` sit inside the argument of
`g`, so continuity in `(t, x)`, up to and including `t = 0`, is one application of dominated
convergence.

## Main results

* `norm_heatOp_le`: `P_t` contracts the supremum norm;
* `heatOpCLM`: `P_t` as a continuous linear map;
* `continuous_heatOp`: `(t, g) ↦ P_t g` is jointly continuous, so `t ↦ P_t g` is a continuous path
  in `C(T³, E)` with `P_0 g = g`;
* `heatOp_torusShift`, `heatOp_compLeftContinuous`: `P_t` commutes with translations and with
  continuous linear maps of the values.
-/
open MeasureTheory Real Filter Topology
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
/-! ### The unit Gaussian -/
public section

/-! ### The integrand -/

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.PDE.continuous_heatOpFun.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  (g : C(RegularityStructures.Torus3, E)),
  Continuous fun (p : ℝ × RegularityStructures.Torus3) ↦
    ∫ (z : Fin 3 → ℝ),
      RegularityStructures.gaussKernel 1 z •
        (g : RegularityStructures.Torus3 → E) (p.2 - RegularityStructures.torusProj (√p.1 • z))
end
/-! ### The operator -/
@[expose] public noncomputable section
/-- The heat operator `P_t g(x) = ∫_{ℝ³} γ₁(z) g(x - √t z) dz` on `C(T³, E)`. It is the heat
semigroup for `t > 0` and the identity for `t ≤ 0`. -/
def heatOp (t : ℝ) (g : C(Torus3, E)) : C(Torus3, E) where
  toFun x := ∫ z : Fin 3 → ℝ, gaussKernel 1 z • g (x - torusProj (√t • z))
  continuous_toFun :=
    (continuous_heatOpFun g).comp (Continuous.prodMk continuous_const continuous_id)
end
public section

variable [CompleteSpace E]

end
@[expose] public noncomputable section
variable [CompleteSpace E]

end
public section

/-! ### Commutation with translations and with linear maps of the values -/
variable [CompleteSpace E] [CompleteSpace F]

end
end RegularityStructures.PDE

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_ceb4ea0fb0d88bbd4a97_Slice ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Time slices of the forcing and the Duhamel integrand `F_t(r)`

For a continuous forcing `f : ℝ × T³ → ℝ` with polynomial growth in time (`PotForcing`), the slices
`f_r = f(r, ·) ∈ C(T³)` depend continuously on `r` (`continuous_potSlice`), and
`potF t r = e^{-(t - r)} P_{t-r} f_r ∈ C(T³)` is continuous in `r` and dominated by
`e^{-(t-r)} B (1 + |r|)^n`, hence integrable on `(-∞, t]` (`integrableOn_potF`).  The massive potential
is `ψ(t) = ∫_{r ≤ t} F_t(r) dr` (see `Phi43.Potential.SlicePotential`).
-/
public section
open MeasureTheory Set Filter Topology
namespace RegularityStructures.Potential
open RegularityStructures

/-- The time slice `f(r, ·)` as a continuous function on `T³`. -/
@[expose] def potSlice {f : SpaceTime → ℝ} (hf : Continuous f) (r : ℝ) : C(Torus3, ℝ) :=
  ⟨fun y => f (r, y), hf.comp (Continuous.prodMk continuous_const continuous_id)⟩

/-- The Duhamel integrand `F_t(r) = e^{-(t-r)} P_{t-r} f_r`. -/
@[expose] noncomputable def potF {f : SpaceTime → ℝ} (hf : Continuous f) (t r : ℝ) :
    C(Torus3, ℝ) :=
  Real.exp (-(t - r)) • PDE.heatOp (t - r) (potSlice hf r)

set_option linter.unusedVariables false in
theorem norm_potF_le {f : SpaceTime → ℝ} {B : ℝ} {n : ℕ} (hB : 0 ≤ B)
    (h : ∀ (r : ℝ) (y : Torus3), |f (r, y)| ≤ B * (1 + |r|) ^ n) (hf : Continuous f) (t r : ℝ) 
    (h_RegularityStructures_Potential_norm_potSlice_le : ∀ {f : RegularityStructures.SpaceTime → ℝ} {B : ℝ} {n : ℕ},
      0 ≤ B →
        (∀ (r : ℝ) (y : RegularityStructures.Torus3), |f (r, y)| ≤ B * (1 + |r|) ^ n) →
          ∀ (hf : Continuous f) (r : ℝ),
            ‖RegularityStructures.Potential.potSlice hf r‖ ≤ B * (1 + |r|) ^ n)
    (h_RegularityStructures_PDE_norm_heatOp_le : ∀ {E : Type} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (t : ℝ)
      (g : C(RegularityStructures.Torus3, E)), ‖RegularityStructures.PDE.heatOp t g‖ ≤ ‖g‖)
    :
    ‖potF hf t r‖ ≤ Real.exp (-(t - r)) * (B * (1 + |r|) ^ n) := by
  unfold potF
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left
    ((h_RegularityStructures_PDE_norm_heatOp_le _ _).trans (h_RegularityStructures_Potential_norm_potSlice_le hB h hf r)) (Real.exp_pos _).le

end RegularityStructures.Potential
end
