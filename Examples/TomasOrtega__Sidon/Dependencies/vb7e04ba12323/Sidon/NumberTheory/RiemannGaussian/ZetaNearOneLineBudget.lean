module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DerivativePowerExponents
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletBlockPowerProfile
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletFullRange
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletPowerParameters
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaDyadicPowerBound
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaDyadicTruncation
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.ZetaNearOneLineBudget
noncomputable section
open RiemannGaussian.DerivativePowerExponents RiemannGaussian.DirichletPowerParameters RiemannGaussian.DerivativeOrderComparison
open RiemannGaussian.DirichletBlockPowerProfile RiemannGaussian.ZetaDyadicTruncation RiemannGaussian.ZetaDyadicPowerBound
theorem norm_le_height_add_one {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 0 ≤ s.im) : ‖s‖ ≤ s.im + 1 := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hσ, abs_of_nonneg ht] at h
  linarith
end
end RiemannGaussian.ZetaNearOneLineBudget
