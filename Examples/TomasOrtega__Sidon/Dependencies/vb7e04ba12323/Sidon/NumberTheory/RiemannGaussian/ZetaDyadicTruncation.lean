module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Data.Nat.Log
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.EtaUniformTailBound
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.EtaZetaPoleBounds
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEta
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.ZetaDyadicTruncation
noncomputable section
open RiemannGaussian.DirichletDyadicBlocks
def remainder (s : ℂ) (J : ℕ) : ℂ := pairedEtaCore s - pairedEtaCorePartialSum (2 ^ J) s
def depth (s : ℂ) : ℕ := Nat.log 2 (⌈‖s‖⌉₊ + 1)
theorem depth_length_lt (s : ℂ) : ((2 ^ depth s : ℕ) : ℝ) < ‖s‖ + 2 := by
  have hp := Nat.pow_log_le_self 2 (show ⌈‖s‖⌉₊ + 1 ≠ 0 by omega)
  have hr : ((2 ^ depth s : ℕ) : ℝ) ≤ ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one (norm_nonneg s)
  push_cast at hr ⊢
  linarith
end
end RiemannGaussian.ZetaDyadicTruncation
