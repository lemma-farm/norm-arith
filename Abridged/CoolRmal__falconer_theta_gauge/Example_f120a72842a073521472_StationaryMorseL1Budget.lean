module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Data.Nat.Factorial.Basic

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.StationaryMorseAngle ====
public section
set_option autoImplicit false
/-!
# The literal Morse coordinate for circular stationary phase
-/
@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace FalconerThetaGauge
def stationaryMorseAngle (s : ℝ) : ℝ := 2 * Real.arcsin (s / 2)
def stationaryMorseJacobian (s : ℝ) : ℝ := (Real.sqrt (1 - s ^ 2 / 4))⁻¹

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.RegularFunctions ====
public section
set_option autoImplicit false
/-!
# Explicit derivative bounds for smooth amplitudes

The global real-line version of Definition 3.1 applies to compactly supported
smooth amplitudes and to periodic lifts of circular amplitudes. The product
bound retains the sum of the two derivative scales exactly.
-/
@[expose] public section
noncomputable section
open Finset
namespace FalconerThetaGauge
/-- Uniform bounds on each actual iterated derivative up to the chosen order. -/
structure IsDerivativeRegular (A M : ℝ) (k : ℕ) (f : ℝ → ℂ) : Prop where
  amplitude_nonneg : 0 ≤ A
  one_le_scale : 1 ≤ M
  smooth : ContDiff ℝ k f
  bound : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ A * M ^ j

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.ExplicitBumpBox ====
public section
set_option autoImplicit false
/-!
# Genuine box smoothing and its explicit derivative cost

The normalized average over a width-`2a` interval is the convolution with the
uniform box probability. The fundamental theorem of calculus identifies its
derivative with the signed endpoint difference. Each such difference costs at
most `a⁻¹` in the actual first norm, uniformly in the smooth input function.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FalconerThetaGauge
/-- The literal normalized uniform-box convolution, expressed as an interval integral. -/
def boxAverage (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * a)⁻¹ * ∫ t in (x - a)..(x + a), f t

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.ExplicitBumpWidths ====
public section
set_option autoImplicit false
/-!
# The explicit box widths and their exact factorial product

The finite-order smoothing construction uses the manuscript's widths
`6/(π² j²)`. Every finite partial sum leaves a positive radius for the smooth
tail, while the first `k` signed differences cost exactly `(π²/6)^k (k!)²`.
-/
@[expose] public section
noncomputable section
open Finset
namespace FalconerThetaGauge
def explicitBoxWidth (j : ℕ) : ℝ := 6 / (Real.pi ^ 2 * (j + 1 : ℝ) ^ 2)

/-- Every finite box convolution leaves genuine room for an arbitrary smooth tail. -/
def explicitBumpTailRadius (K : ℕ) : ℝ := 1 - ∑ j ∈ range K, explicitBoxWidth j
set_option linter.unusedVariables false in
axiom _root_.FalconerThetaGauge.explicitBumpTailRadius_pos : ∀ (K : ℕ), 0 < FalconerThetaGauge.explicitBumpTailRadius K
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.ExplicitBumpStack ====
public section
set_option autoImplicit false
/-!
# Finite stacks of genuine box convolutions

Each derivative may be assigned to the next box, leaving a probability density
behind it. The resulting first-norm estimate depends only on the differentiated
widths, not on the arbitrary smooth tail or the total number of boxes.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge

def explicitBoxStack (j : ℕ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | K + 1, f => boxAverage (explicitBoxWidth j) (explicitBoxStack (j + 1) K f)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.ExplicitBump ====
public section
set_option autoImplicit false
/-!
# Explicit smooth even probability kernels at every finite required order

For any prescribed order `K`, convolve the first `K` uniform boxes of widths
`6/(π²j²)` with an arbitrary normalized smooth even tail in the remaining
support radius. This gives all quantitative derivative estimates through `K`
with exactly the manuscript's constants, without needing an infinite Fourier
product. The source argument uses only finitely many derivatives at each scale.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge

/-- A genuine smooth tail placed in the unused finite support radius. -/
def explicitBumpTail (K : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := explicitBumpTailRadius K / 2
  rOut := explicitBumpTailRadius K
  rIn_pos := by linarith [explicitBumpTailRadius_pos K]
  rIn_lt_rOut := by linarith [explicitBumpTailRadius_pos K]
/-- The actual order-`K` compact smooth probability kernel. -/
def explicitBump (K : ℕ) : ℝ → ℝ :=
  explicitBoxStack 0 K ((explicitBumpTail K).normed volume)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.ExplicitBumpScale ====
public section
set_option autoImplicit false
/-! # Rescaled quantitative finite-order smooth kernels -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
/-- The order-`K` probability kernel at the actual positive spatial scale `δ`. -/
def scaledExplicitBump (K : ℕ) (δ : ℝ) (x : ℝ) : ℝ :=
  δ⁻¹ * explicitBump K (δ⁻¹ * x)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.ExplicitBumpCutoff ====
public section
set_option autoImplicit false
/-! # Actual smooth masks from closed neighborhoods of arbitrary passing sets -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff Convolution
namespace FalconerThetaGauge

/-- A true real-line convolution mask, including masks of periodic sets. -/
def smoothIndicator (K : ℕ) (δ : ℝ) (S : Set ℝ) : ℝ → ℝ :=
  S.indicator (fun _ ↦ 1) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] scaledExplicitBump K δ

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.CircularStationaryCutoff ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # The literal quantitative cutoff at a circular stationary point -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff Convolution
namespace FalconerThetaGauge
/-- Convolve the interval `[-π/4,π/4]` with the order-`K` kernel of radius `π/12`. -/
def circularStationaryCutoff (K : ℕ) : ℝ → ℝ :=
  smoothIndicator K (Real.pi / 12) (Icc (-(Real.pi / 4)) (Real.pi / 4))

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v75f602e882ea.FalconerThetaGauge.StationaryMorseAmplitude ====
public section
set_option autoImplicit false
/-!
# The actual smooth compact amplitude after the circular Morse substitution

The arcsine singularities lie outside the localized support. The literal
product therefore extends smoothly by zero and is supported in [-1,1].
-/
@[expose] public section
noncomputable section
open Set Filter Function
open scoped ContDiff Topology
namespace FalconerThetaGauge
def stationaryMorseAmplitude (χ : ℝ → ℝ) (G : ℝ → ℂ) (φ₀ s : ℝ) : ℂ :=
  (χ (stationaryMorseAngle s) : ℂ) * G (φ₀ + stationaryMorseAngle s) *
    (stationaryMorseJacobian s : ℂ)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Examples.Example_f120a72842a073521472_StationaryMorseL1Budget ====
set_option autoImplicit false
/-! # Literal integral derivative bounds for localized stationary phase -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
set_option linter.unusedVariables false in
/-- The actual integral of the derivative norm is bounded by its support length. -/
theorem integral_norm_iteratedDeriv_stationaryMorseAmplitude_le {K k : ℕ} (hk : k ≤ K)
    {G : ℝ → ℂ} {A M φ : ℝ} (hG : IsDerivativeRegular A M K G) 
    (h_FalconerThetaGauge_circularStationaryCutoff_eq_zero : ∀ (K : ℕ) {x : ℝ}, Real.pi / 3 < |x| → FalconerThetaGauge.circularStationaryCutoff K x = 0)
    (h_FalconerThetaGauge_norm_iteratedDeriv_stationaryMorseAmplitude_le : ∀ {K k : ℕ},
      k ≤ K →
        ∀ {G : ℝ → ℂ} {A M φ s : ℝ},
          FalconerThetaGauge.IsDerivativeRegular A M K G →
            |s| ≤ 1 →
              ‖iteratedDeriv k
                    (FalconerThetaGauge.stationaryMorseAmplitude
                      (FalconerThetaGauge.circularStationaryCutoff K) G φ)
                    s‖ ≤
                2 * A * (56 * M) ^ k * (↑k.factorial : ℝ) ^ 2)
    (h_FalconerThetaGauge_support_stationaryMorseAmplitude_subset : ∀ {χ : ℝ → ℝ},
      (∀ (t : ℝ), Real.pi / 3 < |t| → χ t = 0) →
        ∀ (G : ℝ → ℂ) (φ₀ : ℝ),
          Function.support (FalconerThetaGauge.stationaryMorseAmplitude χ G φ₀) ⊆ Set.Icc (-1) 1)
    (h_FalconerThetaGauge_tsupport_iteratedDeriv_subset : ∀ (k : ℕ) (f : ℝ → ℂ), tsupport (iteratedDeriv k f) ⊆ tsupport f)
    :
    (∫ s : ℝ, ‖iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ) s‖) ≤
      4 * A * (56 * M) ^ k * (k.factorial : ℝ) ^ 2 := by
  let bound := 2 * A * (56 * M) ^ k * (k.factorial : ℝ) ^ 2
  have hsupport : tsupport
      (iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ)) ⊆
        Icc (-1 : ℝ) 1 := by
    apply (h_FalconerThetaGauge_tsupport_iteratedDeriv_subset k _).trans
    exact closure_minimal
      (h_FalconerThetaGauge_support_stationaryMorseAmplitude_subset
        (fun _ hx ↦ h_FalconerThetaGauge_circularStationaryCutoff_eq_zero K hx) G φ) isClosed_Icc
  have hmajor : ∀ s : ℝ,
      ‖iteratedDeriv k (stationaryMorseAmplitude (circularStationaryCutoff K) G φ) s‖ ≤
        (Icc (-1 : ℝ) 1).indicator (fun _ ↦ bound) s := by
    intro s
    by_cases hs : s ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hs]
      exact h_FalconerThetaGauge_norm_iteratedDeriv_stationaryMorseAmplitude_le hk hG (abs_le.mpr hs)
    · rw [indicator_of_notMem hs, image_eq_zero_of_notMem_tsupport
        (fun ht ↦ hs (hsupport ht)), norm_zero]
  have hi : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ ↦ bound)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (isCompact_Icc.measure_ne_top))
  calc
    _ ≤ ∫ s : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ ↦ bound) s :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
        hi (Filter.Eventually.of_forall hmajor)
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_Icc]
      have hv : volume.real (Icc (-1 : ℝ) 1) = 2 := by
        norm_num [Measure.real, Real.volume_Icc]
      simp only [hv, smul_eq_mul, bound]
      ring
end FalconerThetaGauge
