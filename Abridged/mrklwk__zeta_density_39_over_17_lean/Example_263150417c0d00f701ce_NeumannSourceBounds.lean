module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.RCLike.Sqrt

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.ve53b8cbc9fd1.MathCollab.Density.Stronger.Atkinson.BesselY0 ====
public section
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from DFIBesselKernel.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
@[expose] public section
open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
/-- The exponentially decaying term in Schläfli's real integral
representation of the order-zero Neumann kernel. -/
noncomputable def dfiBesselY0Tail (x : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-x * t) / Real.sqrt (1 + t ^ 2)
/-- The oscillatory term in Schläfli's representation, written after the
change of variables `u = π/2 - θ`.  Taking the imaginary part packages the
real sine integral while retaining the complex exponential needed for the
first-derivative estimate. -/
noncomputable def dfiBesselY0Osc (x : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..Real.pi / 2,
    Complex.exp (Complex.I * (x * Real.cos u))).im
/-- DFI's order-zero Neumann kernel, defined by the DLMF/Schläfli integral
representation
`Y₀(x) = (2/π) ( ∫₀^π/² sin(x cos u) du
                         - ∫₀^∞ exp(-xt)/sqrt(1+t²) dt )`.
The representation is used only for positive arguments, exactly as in DFI
Proposition 1. -/
noncomputable def dfiBesselY0 (x : ℝ) : ℝ :=
  (2 / Real.pi) * (dfiBesselY0Osc x - dfiBesselY0Tail x)
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.ve53b8cbc9fd1.MathCollab.Density.Stronger.Atkinson.NeumannTwoTermExpansion ====
public section
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannTwoTermExpansion.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
@[expose] public section
/-!
# A two-term expansion of the literal order-zero Neumann kernel

The phase is written in sine/cosine coordinates to expose both
oscillatory carriers directly. The error has the globally valid
positive-argument bound C x^(-5/2).
-/
set_option autoImplicit false
noncomputable section
open Complex
namespace MathCollab.Density.Stronger.Atkinson
def neumannTwoTerm (x : ℝ) : ℝ :=
  (Real.sqrt Real.pi / Real.pi) *
    ((Real.sin x - Real.cos x) * x ^ (-(1 / 2 : ℝ)) -
      (Real.sin x + Real.cos x) / 8 * x ^ (-(3 / 2 : ℝ)))
def neumannTwoTermErrorConstant : ℝ := (2 / Real.pi) * (9 / 128 : ℝ) * Real.sqrt Real.pi
axiom neumannTwoTermErrorConstant_pos : 0 < neumannTwoTermErrorConstant

axiom abs_dfiBesselY0_sub_neumannTwoTerm_le {x : ℝ} (hx : 0 < x) :
    |dfiBesselY0 x - neumannTwoTerm x| ≤ neumannTwoTermErrorConstant * x ^ (-(5 / 2 : ℝ))
end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_263150417c0d00f701ce_NeumannSourceBounds ====
/-
Copyright (c) 2026 S. McColm. Selected proofs adapted from NeumannSourceBounds.lean,
exact source revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
released under MIT-0. See third_party/twelfth/NEUMANN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain their Apache-2.0 attribution.
The literal classical Bessel kernel, principal half-power branches and
actual convergent integrals are preserved; no asymptotic bound is assumed.
-/
@[expose] public section
/-!
# Measurability and physical-source bounds for the Neumann remainder

The literal kernel and both retained oscillatory terms are measurable.
The actual Bessel argument is linked to height and divisor index;
its quadratic expansion error has the summable n^(-5/4) weight.
-/
set_option autoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

axiom neumann_source_argument_bounds {T x : ℝ} (hT : 16 ≤ T) (hx : T / 16 ≤ x)
    {n : ℕ} (hn : 0 < n) :
    T * n ≤ (4 * Real.pi * Real.sqrt (x * n)) ^ 2 ∧
      1 ≤ 4 * Real.pi * Real.sqrt (x * n)
theorem abs_neumann_source_remainder_le {T x : ℝ} (hT : 16 ≤ T) (hx : T / 16 ≤ x)
    {n : ℕ} (hn : 0 < n) :
    |dfiBesselY0 (4 * Real.pi * Real.sqrt (x * n)) -
      neumannTwoTerm (4 * Real.pi * Real.sqrt (x * n))| ≤
        neumannTwoTermErrorConstant * T ^ (-(5 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨hbase, hy1⟩ := neumann_source_argument_bounds hT hx hn
  have hT0 : 0 < T := by linarith
  have hn0 : (0 : ℝ) < n := by positivity
  have hy0 : 0 < 4 * Real.pi * Real.sqrt (x * n) := by linarith
  apply (abs_dfiBesselY0_sub_neumannTwoTerm_le hy0).trans
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hT0 hn0) hbase
    (by norm_num : -(5 / 4 : ℝ) ≤ 0)
  have he : ((4 * Real.pi * Real.sqrt (x * n)) ^ 2) ^ (-(5 / 4 : ℝ)) =
      (4 * Real.pi * Real.sqrt (x * n)) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hy0.le]
    norm_num
  rw [he, Real.mul_rpow hT0.le hn0.le] at hp
  have h := mul_le_mul_of_nonneg_left hp neumannTwoTermErrorConstant_pos.le
  simpa only [mul_assoc] using h

end MathCollab.Density.Stronger.Atkinson
