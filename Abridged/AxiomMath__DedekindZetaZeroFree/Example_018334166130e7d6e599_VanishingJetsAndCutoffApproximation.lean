module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Examples.Example_018334166130e7d6e599_VanishingJetsAndCutoffApproximation ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation

open scoped ContDiff
open Filter Topology Asymptotics
noncomputable def infinityCutoff (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℂ) :=
  ⟨r / 2, r, by positivity, by linarith⟩

set_option linter.unusedVariables false in
theorem infinityCutoff_derivative_bound (j : ℕ) 
    (h_DedekindZetaZeroFree_KPCplxClosedCellCutoffApproximation_infinityCutoff_scale : ∀ (r : ℝ) (hr : 0 < r),
      (↑(DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation.infinityCutoff r hr) : ℂ → ℝ) =
        fun (u : ℂ) ↦
        (↑(DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation.infinityCutoff 1
                (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl Bool.false))) :
            ℂ → ℝ)
          (r⁻¹ • u))
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r) (u : ℂ),
      ‖iteratedFDeriv ℝ j (infinityCutoff r hr) u‖ ≤ C * (r⁻¹)^j := by
  let b := infinityCutoff 1 (by norm_num)
  have hc : Continuous (iteratedFDeriv ℝ j (b : ℂ → ℝ)) :=
    b.contDiff.continuous_iteratedFDeriv (by simp : (j : ℕ∞ω) ≤ (⊤ : ℕ∞))
  have hs := b.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) j
  have hb := (hs.isCompact_range hc).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr u
  rw [h_DedekindZetaZeroFree_KPCplxClosedCellCutoffApproximation_infinityCutoff_scale r hr, iteratedFDeriv_comp_const_smul r⁻¹
    (b.contDiff (n := (j : ℕ∞)))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (r⁻¹)^j * max C 0 := mul_le_mul_of_nonneg_left
      ((hC _ (Set.mem_range_self (r⁻¹ • u))).trans (le_max_left _ _)) (by positivity)
    _ = _ := mul_comm _ _
end DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation
