module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
/- Compatibility adaptation: explicitly import measurable absolute-value lemmas removed from an upstream transitive import. -/
public import Mathlib
/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
set_option autoImplicit true
set_option linter.deprecated false
@[expose] public section
open MeasureTheory Filter Set Real
open scoped ProbabilityTheory NNReal ENNReal Filter Topology
/-!
# Gaussian integration by parts via exponential tilt (Stein’s identity)

We prove Stein’s lemma and the integration by parts formula for real Gaussian
measures by an explicit control of the exponential tilt and a dominated
differentiation argument. The presentation is self–contained and works in full
generality for one–dimensional (possibly degenerate) Gaussians, under minimal,
standard hypotheses on the test function.

Let `γ_{μ,v}` denote the law of the real normal `N(μ,v)` (variance `v : ℝ≥0`).
For `v ≠ 0` (non-degenerate, centered case) and a test function `F : ℝ → ℝ`
which is `C¹` with polynomial growth (for `F` and `F'`), we show
  E[X F(X)] = v · E[F'(X)]   for X ∼ N(0,v).

The proof follows the canonical route:

1. Exponential tilt and shift:
   For the centered Gaussian density `φ_v(x)`, and `t ∈ ℝ`,
     exp(t x − v t²/2) φ_v(x) = φ_v(x − v t).
   Hence, for every test function `F`,
     E[F(X) exp(tX − v t²/2)] = E[F(X + v t)]  (X ∼ N(0,v)).

2. Difference–quotient bounds:
   We establish sharp, uniform (in `t` near `0`) bounds for
     (exp(t x − v t²/2) − 1)/t,
   derived from the generic inequality `|exp a − 1| ≤ |a| exp |a|`
   and exact algebra on the tilt exponent. This yields an
   exponential–linear integrable majorant after composing with `F`.

3. Dominated differentiation:
   Using the previous step, we differentiate under the integral sign at `t = 0`
   and identify both one–sided derivatives:
     (d/dt)|_{t=0} E[F(X) exp(tX − v t²/2)] = E[X F(X)],
     (d/dt)|_{t=0} E[F(X + v t)]           = v · E[F'(X)].
   Equality of left and right derivatives yields Stein’s identity.

4. Degenerate case:
   If `v = 0`, `γ_{μ,0}` is the Dirac mass at `μ`. All statements reduce to
   trivial identities and are handled uniformly in the API.

Main statements:

- `gaussianTilt_eq_shift`:
    Exponential tilt equals a spatial shift of the test function:
    ∫ F(x) exp(t x − v t²/2) dγ_{0,v}(x) = ∫ F(x + v t) dγ_{0,v}(x).

- `tiltKernel_diffquot_uniform_bound`:
    Uniform (in `t` near `0`) exponential–linear bound for the centered difference quotient
    of the kernel `exp(t x − v t²/2)`.

- `HasModerateGrowth`:
    A simple “polynomial growth” predicate on `F` and `F'` ensuring all integrability
    requirements against a Gaussian. This replaces ad‑hoc, local integrability checks.

- `gaussianTilt_hasDerivAt_left`, `gaussianTilt_hasDerivAt_right`:
    Differentiation under the integral sign at `t = 0` for the tilted functional.

- `stein_lemma_gaussianReal` and `gaussianReal_integration_by_parts`:
    Measure–level statements for `N(0,v)` with `v ≠ 0`.

- `gaussianRV_integration_by_parts` and
  `gaussian_integration_by_parts_general`:
    Random-variable versions for centered and non–centered Gaussians, respectively.

Auxiliary integrability layer:

- Polynomial × sub-Gaussian integrability:
    We prove
      (1+|x|)^k exp(s x²) ∈ L¹(γ_{0,v})
    for every `k : ℕ` whenever either `v = 0` or `s < 1/(2v)`.
    In particular, for `s = 1/(4v)` (non-degenerate) we get the explicit bound
      exp(|x|²/(4v)).
    This is the only analytic input needed for dominated differentiation.

Design notes and future extensions:

- The arguments are written for ℝ and make sharp, explicit use of the 1D tilt
  algebra. The architecture is ready for a finite–dimensional extension
  (`ℝ^n` with the Euclidean norm), where the Cameron–Martin formula replaces
  the 1D tilt identity and the same dominated-differentiation pattern applies.

- The degenerate case is treated uniformly by the Dirac–mass API.

- When interacting with Lebesgue measure, we use the standard `withDensity` and
  `MeasurePreserving` API; addition by a constant is measure–preserving and is
  the canonical tool to implement the change of variables needed in Step 1.

References:
- C. Stein (1972). A bound for the error in the normal approximation to the
  distribution of a sum of dependent random variables.
- M. Talagrand (2011). Upper and Lower Bounds for Stochastic Processes.

-/
namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
end MeasureTheory
variable {Ω : Type*} [MeasureSpace Ω]
namespace ProbabilityTheory
/-- A random variable `g` is Gaussian with mean `μ` and variance `v` if its law is
`gaussianReal μ v`. -/
def IsGaussianRV (g : Ω → ℝ) (μ : ℝ) (v : ℝ≥0) : Prop :=
  Measure.map g ℙ = gaussianReal μ v
/-- A random variable `g` is centered Gaussian with variance `v` if its law is
`gaussianReal 0 v`. -/
def IsCenteredGaussianRV (g : Ω → ℝ) (v : ℝ≥0) : Prop :=
  IsGaussianRV g 0 v
def HasModerateGrowth (F : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), 0 < C ∧
    (∀ x, |F x| ≤ C * (1 + |x|)^m) ∧
    (∀ x, |deriv F x| ≤ C * (1 + |x|)^m)
section DominationExponentialUpgrade
variable {v : ℝ≥0} {δ : ℝ}
/-! ### Elementary linear–quadratic “Young” bounds  -/
section YoungBounds
open Real
namespace Real
open Real
end Real
open Real
section YoungBounds
open Real
namespace Measure
open MeasureTheory
end Measure
open Measure
/-!
### Structured domination lemmas for `( |x| + B )^k` and Gaussian integrability

We factor the proof of
`Integrable fun x => (|x| + 2)^k * exp (-a * x^2)`
into small reusable lemmas.  The bound is intentionally *coarse* but
polynomial × Gaussian is always integrable, so sharp constants are irrelevant.
-/
section PolyGaussianDomination
namespace Real
end Real
open Real
end PolyGaussianDomination
open ProbabilityTheory
/-! ### Polynomial moment integrability -/
section GaussianPolynomialMomentRewrite
variable {v : ℝ≥0} (hv : v ≠ 0) (k : ℕ)
end GaussianPolynomialMomentRewrite
end YoungBounds
end YoungBounds
end DominationExponentialUpgrade
end ProbabilityTheory
