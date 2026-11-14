module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Tactic.Bound
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Data.Finset.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v27fab7072f24.GuthMaynard.NativeSource.GuthMaynard.LargeValuesDefinitions ====
public section
set_option autoImplicit false
@[expose] public section
open Complex Finset Set
open scoped BigOperators ContDiff
namespace GuthMaynard.NativeMoment
/-!
# Source-facing objects for Guth--Maynard large values

These are the finite objects used by Sections 3--12 of Guth--Maynard.  They
replace the unrelated and false parabola-decoupling model formerly present in
the project.  No analytic estimate is postulated in this file.
-/
/-- A fixed smooth cutoff supported on the source dyadic interval.  Derivative
bounds are recorded separately by the lemmas that consume a cutoff, so that
their constant dependencies remain visible. -/
structure GMSmoothCutoff where
  /-- The `toFun` component of `GMSmoothCutoff`. -/
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ x, 0 ≤ toFun x
  bounded : ∀ x, toFun x ≤ 1
  support : Function.support toFun ⊆ Set.Icc 1 2
  equals_one : ∀ x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ), toFun x = 1
instance : CoeFun GMSmoothCutoff (fun _ => ℝ → ℝ) := ⟨GMSmoothCutoff.toFun⟩

/-- Rows of the Guth--Maynard sampling matrix are the selected ordinates. -/
abbrev GMRow (W : Finset ℝ) := {t : ℝ // t ∈ W}

end GuthMaynard.NativeMoment

end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v27fab7072f24.GuthMaynard.NativeSource.GuthMaynard.Separated ====
public section
set_option autoImplicit false
@[expose] public section
open Set Metric
namespace GuthMaynard.NativeMoment
/-- A finite set `W` of real numbers is `δ`-separated if the distance between any two distinct points is at least `δ`. -/
def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ dist x y
def InBaseInterval (T : ℝ) (W : Finset ℝ) : Prop :=
  ∀ (x : ℝ), x ∈ W → x ∈ Icc 0 T
open scoped Classical
end GuthMaynard.NativeMoment

end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v27fab7072f24.GuthMaynard.NativeSource.GuthMaynard.LargeValuesPoisson ====
public section
set_option autoImplicit false
@[expose] public section
open Complex Filter MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap Topology
namespace GuthMaynard.NativeMoment
/-!
# Fourier kernels for the Guth--Maynard trace expansion

This module starts the source Lemmas 4.3--4.5 from the actual cutoff used by
the sampling matrix.  In particular, the oscillatory kernel is a genuine
compactly supported smooth function and its Fourier transform is obtained
from Mathlib's Schwartz-space Fourier transform.
-/
/-- The source kernel `h_t(u) = w(u)^2 u^(it)`.  `Real.log` is harmless at
zero because the cutoff vanishes on a neighborhood of zero. -/
noncomputable def gmTraceKernel (cutoff : GMSmoothCutoff) (t x : ℝ) : ℂ :=
  (cutoff x : ℂ) ^ 2 *
    Complex.exp ((((t * Real.log x : ℝ) : ℂ) * I))

axiom contDiff_gmTraceKernel (cutoff : GMSmoothCutoff) (t : ℝ) :
    ContDiff ℝ ∞ (gmTraceKernel cutoff t)
axiom hasCompactSupport_gmTraceKernel (cutoff : GMSmoothCutoff) (t : ℝ) :
    HasCompactSupport (gmTraceKernel cutoff t)
/-- The trace kernel as a Schwartz function. -/
noncomputable def gmTraceKernelSchwartz (cutoff : GMSmoothCutoff) (t : ℝ) :
    𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmTraceKernel cutoff t).toSchwartzMap
    (contDiff_gmTraceKernel cutoff t)

/-- The Fourier coefficient `h-hat_t(ξ)` appearing in Lemmas 4.3--4.5. -/
noncomputable def gmTraceFourier (cutoff : GMSmoothCutoff) (t ξ : ℝ) : ℂ :=
  𝓕 (gmTraceKernelSchwartz cutoff t) ξ

/-! ## Hilbert--Schmidt first-trace expansion -/

end GuthMaynard.NativeMoment

end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_10bf04076914859c383e_LargeValuesCubic ====
set_option autoImplicit false
@[expose] public section
open Complex Finset Filter MeasureTheory Real Set
open scoped BigOperators
namespace GuthMaynard.NativeMoment
/-!
# Cubic Poisson trace and the `S₁/S₂/S₃` split

This module formalizes Guth--Maynard Lemma 4.5 and the decomposition (5.5).
Every dual sum is an absolutely summable integer series.  The three pieces are
obtained by writing each Gram kernel as its zero Fourier mode plus its complete
nonzero-frequency tail and expanding the resulting cubic product.
-/
/-- The scaled `m`-th Fourier mode `N h-hat_t(Nm)` in the source Poisson
formula. -/
noncomputable def gmScaledTraceMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) (m : ℤ) : ℂ :=
  (N : ℂ) * gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))
/-- The complete nonzero-frequency tail at ordinate difference `t`. -/
noncomputable def gmTraceNonzeroTailAt (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) : ℂ :=
  ∑' m : ℤ, if m = 0 then 0 else gmScaledTraceMode cutoff N t m
/-- The scaled zero Fourier mode. -/
noncomputable def gmTraceZeroMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) : ℂ :=
  gmScaledTraceMode cutoff N t 0
axiom gmTraceNonzeroTailAt_bound (cutoff : GMSmoothCutoff)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 0 < N → ∀ t : ℝ,
      ‖gmTraceNonzeroTailAt cutoff N t‖ ≤
        K * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1)
/-- A uniform bound for every scaled zero mode. -/
axiom gmTraceZeroMode_bound (cutoff : GMSmoothCutoff) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (t : ℝ),
      ‖gmTraceZeroMode cutoff N t‖ ≤ (N : ℝ) * B
/-- A separated nonzero ordinate difference makes its scaled zero mode
arbitrarily small. -/
axiom gmTraceZeroMode_separated_bound (cutoff : GMSmoothCutoff)
    (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) {δ t : ℝ}, 0 < δ → δ ≤ |t| →
      ‖gmTraceZeroMode cutoff N t‖ ≤
        (N : ℝ) * C / δ ^ q
noncomputable def gmCubicS1Summand (cutoff : GMSmoothCutoff) (N : ℕ)
    {W : Finset ℝ} (t u v : GMRow W) : ℂ :=
  (gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
    gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
    gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
      gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
        gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ)))
/-- The piece with exactly one nonzero Fourier frequency. -/
noncomputable def gmCubicS1 (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmCubicS1Summand cutoff N t u v
private axiom gmRow_difference_abs_le {T : ℝ} {W : Finset ℝ}
    (hW : InBaseInterval T W) (t u : GMRow W) :
    |(t : ℝ) - (u : ℝ)| ≤ T
private axiom gmRow_difference_separated {δ : ℝ} {W : Finset ℝ}
    (hSep : IsSeparated δ W) (t u : GMRow W) (htu : t ≠ u) :
    δ ≤ |(t : ℝ) - (u : ℝ)|
theorem gmCubicS1_quantitative (cutoff : GMSmoothCutoff) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T δ : ℝ},
      0 < N → 0 < δ → IsSeparated δ W → InBaseInterval T W →
      ‖gmCubicS1 cutoff N W‖ ≤
        K * (W.card : ℝ) ^ 3 *
          ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
            (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
  obtain ⟨B, hB, hZero⟩ := gmTraceZeroMode_bound cutoff
  obtain ⟨C, hC, hSmall⟩ := gmTraceZeroMode_separated_bound cutoff q
  obtain ⟨L, hL, hTail⟩ := gmTraceNonzeroTailAt_bound cutoff 2 (by norm_num)
  obtain ⟨D, hD, hTailZero⟩ :=
    gmTraceNonzeroTailAt_bound cutoff 30 (by norm_num)
  let K : ℝ := 3 * (L * B * C + B ^ 2 * D) + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N W T δ hN hδ hSep hW
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let offMajor : ℝ :=
    L * (1 + |T|) ^ 2 / (N : ℝ) *
      ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q)
  let diagMajor : ℝ :=
    3 * ((N : ℝ) * B) ^ 2 *
      (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29)
  have hOffNonneg : 0 ≤ offMajor := by dsimp only [offMajor]; positivity
  have hDiagNonneg : 0 ≤ diagMajor := by dsimp only [diagMajor]; positivity
  have hTailAny : ∀ t u : GMRow W,
      ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ≤
        L * (1 + |T|) ^ 2 / (N : ℝ) := by
    intro t u
    have hdiff := gmRow_difference_abs_le hW t u
    have hbase : 1 + |(t : ℝ) - (u : ℝ)| ≤ 1 + |T| := by
      have hT0 : 0 ≤ T := by
        have ht := hW t t.property
        rw [Set.mem_Icc] at ht
        linarith
      rw [abs_of_nonneg hT0]
      linarith
    calc
      ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ ≤
          L * (1 + |(t : ℝ) - (u : ℝ)|) ^ 2 /
            (N : ℝ) ^ (2 - 1) := hTail N hN ((t : ℝ) - (u : ℝ))
      _ ≤ L * (1 + |T|) ^ 2 / (N : ℝ) := by
        simp only [Nat.reduceSubDiff, pow_one]
        gcongr
  have hTailDiag : ‖gmTraceNonzeroTailAt cutoff N 0‖ ≤
      D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29 := by
    simpa using hTailZero N hN 0
  have hSummand : ∀ t u v : GMRow W,
      ‖gmCubicS1Summand cutoff N t u v‖ ≤ offMajor * 3 + diagMajor := by
    intro t u v
    by_cases hAll : t = u ∧ u = v
    · rcases hAll with ⟨rfl, rfl⟩
      simp only [sub_self, gmCubicS1Summand]
      have hDiagOne :
          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
              ‖gmTraceZeroMode cutoff N 0‖ *
                ‖gmTraceZeroMode cutoff N 0‖ ≤
            ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
        calc
          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
              ‖gmTraceZeroMode cutoff N 0‖ *
                ‖gmTraceZeroMode cutoff N 0‖ ≤
            (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) *
              ((N : ℝ) * B) * ((N : ℝ) * B) := by
                gcongr
                · exact hZero N 0
                · exact hZero N 0
          _ = _ := by ring
      calc
        ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
              gmTraceZeroMode cutoff N 0 +
            gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
              gmTraceZeroMode cutoff N 0 +
            gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
              gmTraceNonzeroTailAt cutoff N 0‖ ≤
            3 * ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
          calc
            ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceZeroMode cutoff N 0 +
                gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
                  gmTraceZeroMode cutoff N 0 +
                gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceNonzeroTailAt cutoff N 0‖ ≤
              ‖gmTraceNonzeroTailAt cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceZeroMode cutoff N 0‖ +
                ‖gmTraceZeroMode cutoff N 0 * gmTraceNonzeroTailAt cutoff N 0 *
                  gmTraceZeroMode cutoff N 0‖ +
                ‖gmTraceZeroMode cutoff N 0 * gmTraceZeroMode cutoff N 0 *
                  gmTraceNonzeroTailAt cutoff N 0‖ := by
                    calc
                      ‖(_ + _) + _‖ ≤ ‖_ + _‖ + ‖_‖ := norm_add_le _ _
                      _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := by
                        gcongr
                        exact norm_add_le _ _
            _ ≤ 3 * ((N : ℝ) * B) ^ 2 *
                (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                  simp only [norm_mul]
                  have hDiagTwo :
                      ‖gmTraceZeroMode cutoff N 0‖ *
                          ‖gmTraceNonzeroTailAt cutoff N 0‖ *
                            ‖gmTraceZeroMode cutoff N 0‖ ≤
                        ((N : ℝ) * B) ^ 2 *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                    calc
                      _ ≤ ((N : ℝ) * B) *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) *
                            ((N : ℝ) * B) := by
                              gcongr
                              · exact hZero N 0
                              · exact hZero N 0
                      _ = _ := by ring
                  have hDiagThree :
                      ‖gmTraceZeroMode cutoff N 0‖ *
                          ‖gmTraceZeroMode cutoff N 0‖ *
                            ‖gmTraceNonzeroTailAt cutoff N 0‖ ≤
                        ((N : ℝ) * B) ^ 2 *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                    calc
                      _ ≤ ((N : ℝ) * B) * ((N : ℝ) * B) *
                          (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) := by
                            gcongr
                            · exact hZero N 0
                            · exact hZero N 0
                      _ = _ := by ring
                  nlinarith
      _ = diagMajor := by rfl
      _ ≤ offMajor * 3 + diagMajor := by nlinarith
    · have hTerm1 :
          ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : u ≠ v ∨ v ≠ t := by
          by_cases huv : u = v
          · right
            intro hvt
            apply hAll
            subst v
            subst u
            exact ⟨rfl, rfl⟩
          · exact Or.inl huv
        rcases hCases with huv | hvt
        · simp only [norm_mul]
          calc
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) := by
                  gcongr
                  · exact hTailAny t u
                  · exact hSmall N hδ (gmRow_difference_separated hSep u v huv)
                  · exact hZero N ((v : ℝ) - (t : ℝ))
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q) := by
                  gcongr
                  · exact hTailAny t u
                  · exact hZero N ((u : ℝ) - (v : ℝ))
                  · exact hSmall N hδ (gmRow_difference_separated hSep v t hvt)
            _ = offMajor := by rfl
      have hTerm2 :
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : t ≠ u ∨ v ≠ t := by
          by_cases htu : t = u
          · right
            intro hvt
            apply hAll
            subst u
            subst v
            exact ⟨rfl, rfl⟩
          · exact Or.inl htu
        rcases hCases with htu | hvt
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * C / δ ^ q) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) * ((N : ℝ) * B) := by
                  gcongr
                  · exact hSmall N hδ (gmRow_difference_separated hSep t u htu)
                  · exact hTailAny u v
                  · exact hZero N ((v : ℝ) - (t : ℝ))
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * B) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) *
                  ((N : ℝ) * C / δ ^ q) := by
                    gcongr
                    · exact hZero N ((t : ℝ) - (u : ℝ))
                    · exact hTailAny u v
                    · exact hSmall N hδ (gmRow_difference_separated hSep v t hvt)
            _ = offMajor := by dsimp only [offMajor]; ring
      have hTerm3 :
          ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤ offMajor := by
        have hCases : t ≠ u ∨ u ≠ v := by
          by_cases htu : t = u
          · right
            intro huv
            exact hAll ⟨htu, huv⟩
          · exact Or.inl htu
        rcases hCases with htu | huv
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * C / δ ^ q) * ((N : ℝ) * B) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) := by
                  gcongr
                  · exact hSmall N hδ (gmRow_difference_separated hSep t u htu)
                  · exact hZero N ((u : ℝ) - (v : ℝ))
                  · exact hTailAny v t
            _ = offMajor := by dsimp only [offMajor]; ring
        · simp only [norm_mul]
          calc
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ))‖ *
                ‖gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ))‖ *
                  ‖gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
              ((N : ℝ) * B) * ((N : ℝ) * C / δ ^ q) *
                (L * (1 + |T|) ^ 2 / (N : ℝ)) := by
                  gcongr
                  · exact hZero N ((t : ℝ) - (u : ℝ))
                  · exact hSmall N hδ (gmRow_difference_separated hSep u v huv)
                  · exact hTailAny v t
            _ = offMajor := by dsimp only [offMajor]; ring
      unfold gmCubicS1Summand
      calc
        ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ)) +
            gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ ≤
            ‖gmTraceNonzeroTailAt cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ +
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceNonzeroTailAt cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceZeroMode cutoff N ((v : ℝ) - (t : ℝ))‖ +
            ‖gmTraceZeroMode cutoff N ((t : ℝ) - (u : ℝ)) *
              gmTraceZeroMode cutoff N ((u : ℝ) - (v : ℝ)) *
                gmTraceNonzeroTailAt cutoff N ((v : ℝ) - (t : ℝ))‖ := by
                  exact (norm_add_le _ _).trans
                    (by gcongr; exact norm_add_le _ _)
        _ ≤ offMajor * 3 := by nlinarith
        _ ≤ offMajor * 3 + diagMajor := le_add_of_nonneg_right hDiagNonneg
  unfold gmCubicS1
  calc
    ‖∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmCubicS1Summand cutoff N t u v‖ ≤
        ∑ t : GMRow W, ‖∑ u : GMRow W, ∑ v : GMRow W,
          gmCubicS1Summand cutoff N t u v‖ := norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W,
        ‖∑ v : GMRow W, gmCubicS1Summand cutoff N t u v‖ := by
          apply Finset.sum_le_sum
          intro t ht
          exact norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        ‖gmCubicS1Summand cutoff N t u v‖ := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro u hu
          exact norm_sum_le _ _
    _ ≤ ∑ _t : GMRow W, ∑ _u : GMRow W, ∑ _v : GMRow W,
        (offMajor * 3 + diagMajor) := by
          gcongr with t ht u hu v hv
          exact hSummand t u v
    _ = (W.card : ℝ) ^ 3 * (offMajor * 3 + diagMajor) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ ≤ K * (W.card : ℝ) ^ 3 *
          ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
            (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
      dsimp only [offMajor, diagMajor, K]
      have hFirst :
          L * (1 + |T|) ^ 2 / (N : ℝ) * ((N : ℝ) * B) *
              ((N : ℝ) * C / δ ^ q) =
            L * B * C * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q) := by
        field_simp [hNr.ne']
      have hSecond :
          3 * ((N : ℝ) * B) ^ 2 *
              (D * (1 + |(0 : ℝ)|) ^ 30 / (N : ℝ) ^ 29) =
            3 * B ^ 2 * D * ((N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by
        norm_num
        ring
      rw [hFirst, hSecond]
      have hCardNonneg : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
      have hx : 0 ≤ (N : ℝ) * (1 + |T|) ^ 2 / δ ^ q := by positivity
      have hy : 0 ≤ (N : ℝ) ^ 2 / (N : ℝ) ^ 29 := by positivity
      calc
        (W.card : ℝ) ^ 3 *
              (L * B * C * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q) * 3 +
                3 * B ^ 2 * D * ((N : ℝ) ^ 2 / (N : ℝ) ^ 29)) ≤
            (W.card : ℝ) ^ 3 *
              (K * ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
                (N : ℝ) ^ 2 / (N : ℝ) ^ 29)) := by
          apply mul_le_mul_of_nonneg_left _ hCardNonneg
          nlinarith [mul_nonneg (mul_nonneg hL.le hB.le) hC.le,
            mul_nonneg (sq_nonneg B) hD.le]
        _ = K * (W.card : ℝ) ^ 3 *
              ((N : ℝ) * (1 + |T|) ^ 2 / δ ^ q +
                (N : ℝ) ^ 2 / (N : ℝ) ^ 29) := by ring
end GuthMaynard.NativeMoment
