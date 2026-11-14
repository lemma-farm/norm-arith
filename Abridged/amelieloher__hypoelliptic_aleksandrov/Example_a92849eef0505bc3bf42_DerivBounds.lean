module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Set.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.NormNum
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.PDEFoundation.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/
@[expose] public section
namespace PDE
/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.HypoellipticAleksandrov.KineticAleksandrov.MovingKernel ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moving-fiber kernels

This module fixes the carrier for the terminal evolution kernel.  Invalid
time pairs and off-domain source states have no values: the master kernel is
defined only on the corresponding valid-query subtype.  Fixed-time kernels
are obtained from that one master kernel by `Kernel.comap` and
`Kernel.comapRight`.
-/
@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ProbabilityTheory
namespace HypoellipticAleksandrov.KineticAleksandrov
/-- The ambient fixed-time state `(y, z)`. -/
abbrev EvolutionAmbientState (n : ℕ) := PDE.Vec n × PDE.Vec n

namespace MovingFiberKernel
end MovingFiberKernel
namespace MovingFiberKernel
end MovingFiberKernel
end HypoellipticAleksandrov.KineticAleksandrov

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate derivatives on phase space

Phase-space points are `y = (v, z) : EvolutionAmbientState d`, velocity first, as in the terminal
solution operator. This module fixes the coordinate partial derivatives and the second-order
operators used throughout the full-coefficient Aleksandrov estimate: velocity and position partials,
the velocity Hessian contraction
`B : D_v² F`, the transport derivative `v · ∇_z F`, the two Laplacians and the mixed operator
`∇_z · ∇_v`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
/-- The `i`-th velocity partial derivative of a function on phase space `(v, z)`. -/
def velocityPartial (i : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (Pi.single i 1, 0)
/-- The `i`-th position partial derivative of a function on phase space `(v, z)`. -/
def positionPartial (i : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (0, Pi.single i 1)
def velocityLaplacian (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, velocityPartial i (velocityPartial i F) y
/-- The position Laplacian `Δ_z F`. -/
def positionLaplacian (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, positionPartial i (positionPartial i F) y
/-- The mixed operator `∇_z · ∇_v F = ∑ᵢ ∂_{zᵢ} ∂_{vᵢ} F`. -/
def mixedDivergence (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, positionPartial i (velocityPartial i F) y
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.ParametricIntegral ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth dependence of weighted convolutions with finite measures

For a finite measure `m` on a normed space `E`, a bounded measurable weight `f : E → ℝ` and a
function `G : E → F` all of whose derivatives are bounded, the weighted convolution
`y ↦ ∫ f a • G (y - a) ∂m` is smooth and its Fréchet derivative is the weighted convolution of
`fderiv G`. This is the analytic content of the smoothness of the smoothed
functions: differentiation under the integral sign in the space variable.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
universe u
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

section Measure
variable [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
/-- The weighted convolution `y ↦ ∫ f a • G (y - a) ∂m`. -/
def wconv (G : E → F) (f : E → ℝ) (m : Measure E) (y : E) : F :=
  ∫ a, f a • G (y - a) ∂m

end Measure
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coordinates ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate partial derivatives and their norms

All `2d` coordinate directions of phase space `(v, z)` are indexed by `Fin d ⊕ Fin d`
(velocity coordinates on the left, position coordinates on the right). This module records the
squared gradient and Hessian norms used in the smoothing estimates, their comparison with the
operator norms of the Fréchet derivatives,
and the commutation of coordinate partials with weighted convolutions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
/-- The unit vector of phase space in the coordinate direction `c`. -/
def coordDir : Fin d ⊕ Fin d → EvolutionAmbientState d
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)
/-- The partial derivative in the coordinate direction `c`. -/
def coordPartial (c : Fin d ⊕ Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (coordDir c)

axiom abs_coordPartial_coordPartial_le {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c c' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    |coordPartial c (coordPartial c' F) y| ≤ ‖iteratedFDeriv ℝ 2 F y‖
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Kernel ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Abstract smoothing kernel families

`SmoothingKernelFamily d lam` packages exactly the properties of the Gaussian flow kernel
`Φ_h` that the smoothing estimates use:
positivity, smoothness in the phase variable, unit mass, the sup bound, the heat equation in `h`
with generator `(lam/2) (2 h² Δ_z - 2 h ∇_z·∇_v + Δ_v)`, and the derivative, moment and
integrability bounds of the Gaussian flow, locally uniformly in `h` on compact subsets of `(0,∞)`.
Every smoothing estimate is then proved for an arbitrary such family.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
/-- The generator `M^h : D²F = (lam/2) (2 h² Δ_z F - 2 h ∇_z·∇_v F + Δ_v F)` of the flow. -/
def heatOperator (lam h : ℝ) (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    ℝ :=
  lam / 2 * (2 * h ^ 2 * positionLaplacian F y - 2 * h * mixedDivergence F y +
    velocityLaplacian F y)
/-- An abstract family of smoothing kernels `Φ_h` on phase space, with the properties of
the Gaussian flow used by the smoothing estimates. -/
structure SmoothingKernelFamily (d : ℕ) (lam : ℝ) where
  /-- The kernel `Φ_h(y)`. -/
  kernel : ℝ → EvolutionAmbientState d → ℝ
  /-- The constant `c_{d,λ}` with `Φ_h ≤ c_{d,λ} h^{-2d}`. -/
  supConst : ℝ
  pos : ∀ {h : ℝ}, 0 < h → ∀ y, 0 < kernel h y
  contDiff : ∀ {h : ℝ}, 0 < h → ContDiff ℝ (⊤ : ℕ∞) (kernel h)
  integral_eq_one : ∀ {h : ℝ}, 0 < h → ∫ y, kernel h y = 1
  le_sup : ∀ {h : ℝ}, 0 < h → ∀ y, kernel h y ≤ supConst * (h ^ (2 * d))⁻¹
  hasDerivAt_heat : ∀ {h : ℝ}, 0 < h → ∀ y,
    HasDerivAt (fun s => kernel s y) (heatOperator lam h (kernel h) y) h
  deriv_bound : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ C : ℝ, ∀ h ∈ K, ∀ y, ‖iteratedFDeriv ℝ k (kernel h) y‖ ≤ C * (1 + ‖y‖) ^ k * kernel h y
  weight_le : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ C : ℝ, ∀ h ∈ K, ∀ y, (1 + ‖y‖) ^ k * kernel h y ≤ C
  weight_integrable : ∀ (k : ℕ) {h : ℝ}, 0 < h →
    Integrable (fun y => (1 + ‖y‖) ^ k * kernel h y)
  weight_integral_le : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ C : ℝ, ∀ h ∈ K, ∫ y, (1 + ‖y‖) ^ k * kernel h y ≤ C
  /-- Joint continuity of `(h, y) ↦ Φ_h(y)` on `(0, ∞) × ℝ^{2d}`. -/
  joint : ContinuousOn (fun p : ℝ × EvolutionAmbientState d => kernel p.1 p.2)
    (Set.Ioi 0 ×ˢ Set.univ)
  /-- A single bounded continuous integrable function dominating the weighted kernels
  `(1 + ‖y‖)^k Φ_h`, uniformly for `h` in a compact subset of `(0, ∞)`. -/
  weight_dom : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ (G : EvolutionAmbientState d → ℝ) (B : ℝ), Continuous G ∧ Integrable G ∧
      (∀ z, 0 ≤ G z ∧ G z ≤ B) ∧ ∀ h ∈ K, ∀ z, (1 + ‖z‖) ^ k * kernel h z ≤ G z
namespace SmoothingKernelFamily
variable {lam : ℝ} (Φ : SmoothingKernelFamily d lam)

end SmoothingKernelFamily
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Convolution ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Weighted smoothing of finite measures: differentiation in the phase variable

For a bounded measurable weight `f` and a finite measure `m` on phase space, the weighted
smoothing `y ↦ ∫ Φ_h(y - y') f(y') ∂m(y')` is smooth, and coordinate partial derivatives are taken
under the integral sign.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}

variable {lam : ℝ} (Φ : SmoothingKernelFamily d lam)
/-- The `f`-weighted smoothing `y ↦ ∫ Φ_h(y - y') f(y') dm(y')`. -/
def smoothWeighted (h : ℝ) (f : EvolutionAmbientState d → ℝ)
    (m : Measure (EvolutionAmbientState d)) : EvolutionAmbientState d → ℝ :=
  wconv (Φ.kernel h) f m

variable {Φ} {h : ℝ} {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  {m : Measure (EvolutionAmbientState d)} [IsFiniteMeasure m]

axiom coordPartial₂_smoothWeighted (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (c c' : Fin d ⊕ Fin d) :
    coordPartial c' (coordPartial c (smoothWeighted Φ h f m)) =
      wconv (coordPartial c' (coordPartial c (Φ.kernel h))) f m
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Weights ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The weighted smoothing `∫ (1 + |y - y'|)² Φ_h(y - y') dm(y')`

Every integrand of the smoothing estimates is bounded by a constant times this single function. This
module proves the bounds of the smoothed weighted measures and of their
first and second coordinate partials by it, using the derivative bounds of the Gaussian flow
estimates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam)
/-- The weighted kernel `(1 + |z|)² Φ_h(z)`. -/
def weight2 (h : ℝ) (z : EvolutionAmbientState d) : ℝ := (1 + ‖z‖) ^ 2 * Φ.kernel h z
/-- The `m`-smoothing of the weighted kernel. -/
def smoothWeight2 (h : ℝ) (m : Measure (EvolutionAmbientState d)) (y : EvolutionAmbientState d) :
    ℝ :=
  ∫ a, weight2 Φ h (y - a) ∂m
variable {Φ} {h : ℝ}

variable (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_a92849eef0505bc3bf42_DerivBounds ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Bounds of weighted smoothings and their partials by `∫ (1 + |y - y'|)² Φ_h dm`

For a bounded measurable weight `f` (`|f| ≤ Cf`), the weighted smoothing of `m` and its first and
second coordinate partials are bounded pointwise by `Cf`, `Cf |C₁|`, `Cf |C₂|` times
`smoothWeight2`, where `C_k` is the constant of the derivative bound of the Gaussian flow estimates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ} {lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h : ℝ}
  {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]
axiom abs_integral_weighted_le {g : EvolutionAmbientState d → ℝ} (hh : 0 < h)
    (y : EvolutionAmbientState d) (A : ℝ)
    (hg : ∀ a, |f a * g (y - a)| ≤ A * weight2 Φ h (y - a)) :
    |∫ a, f a * g (y - a) ∂m| ≤ A * smoothWeight2 Φ h m y
theorem abs_coordPartial₂_smoothWeighted_le (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) {C2 : ℝ}
    (hC2 : ∀ z, ‖iteratedFDeriv ℝ 2 (Φ.kernel h) z‖ ≤ C2 * (1 + ‖z‖) ^ 2 * Φ.kernel h z)
    (c c' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    |coordPartial c' (coordPartial c (smoothWeighted Φ h f m)) y| ≤
      Cf * |C2| * smoothWeight2 Φ h m y := by
  rw [coordPartial₂_smoothWeighted hh hf hfb c c']
  refine abs_integral_weighted_le (g := coordPartial c' (coordPartial c (Φ.kernel h))) m hh y
    (Cf * |C2|) (fun a => ?_)
  have h1 := abs_coordPartial_coordPartial_le (Φ.contDiff hh) c' c (y - a)
  have h2 : ‖iteratedFDeriv ℝ 2 (Φ.kernel h) (y - a)‖ ≤ |C2| * weight2 Φ h (y - a) := by
    refine (hC2 (y - a)).trans ?_
    have hp := Φ.pos hh (y - a)
    unfold weight2
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  rw [abs_mul]
  calc |f a| * |coordPartial c' (coordPartial c (Φ.kernel h)) (y - a)|
      ≤ Cf * (|C2| * weight2 Φ h (y - a)) :=
        mul_le_mul (hfb a) (h1.trans h2) (abs_nonneg _) ((abs_nonneg _).trans (hfb a))
    _ = Cf * |C2| * weight2 Φ h (y - a) := by ring
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
