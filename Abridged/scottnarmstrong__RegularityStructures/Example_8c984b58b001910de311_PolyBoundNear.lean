module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Convolution

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.RegularityStructure ====
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
# Regularity structures with a graded basis

A regularity structure `𝒯 = (A, T, G)` [Hai14, Definition 2.1] is recorded through a graded basis:
a finite index type `ι` and degrees `deg : ι → ℝ`. The model space is `T = ι → ℝ`, with basis
vectors `e_i = Pi.single i 1`, and

* `T_α = homogeneousSubspace deg α = span {e_i : deg i = α}`;
* `T_{<α} = lowerSubspace deg α = span {e_i : deg i < α}`.

The index set `A = deg '' univ` is finite, hence bounded below and locally finite. Every
finite-dimensional graded space has a graded basis, so this loses no generality for finite
sectors; the norm `|τ|_α` is replaced by the equivalent coordinatewise bounds. The structure
group is a subgroup `G` of `GL(T)` whose elements are *graded unipotent*:
`Γ τ - τ ∈ T_{<α}` for `τ ∈ T_α` (`isGradedUnipotent_iff`).

Source: [Hai14] = arXiv:1303.5113v4, Definition 2.1; [Hos25] = arXiv:2310.07396v2,
Definition 3.1.
-/
@[expose] public noncomputable section
namespace RegularityStructures
variable {ι : Type*}
/-- The homogeneous subspace `T_α = span {e_i : deg i = α}`. -/
def homogeneousSubspace (deg : ι → ℝ) (α : ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {τ | ∀ i, deg i ≠ α → τ i = 0}
  add_mem' {τ σ} hτ hσ i hi := by simp [hτ i hi, hσ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c τ hτ i hi := by simp [hτ i hi]
/-- The subspace `T_{<α} = span {e_i : deg i < α}`. -/
def lowerSubspace (deg : ι → ℝ) (α : ℝ) : Submodule ℝ (ι → ℝ) where
  carrier := {τ | ∀ i, α ≤ deg i → τ i = 0}
  add_mem' {τ σ} hτ hσ i hi := by simp [hτ i hi, hσ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c τ hτ i hi := by simp [hτ i hi]
/-- A linear map is graded unipotent if `Γ e_i - e_i ∈ T_{<deg i}` for every basis vector. -/
def IsGradedUnipotent [DecidableEq ι] (deg : ι → ℝ) (Γ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop :=
  ∀ i, Γ (Pi.single i 1) - Pi.single i 1 ∈ lowerSubspace deg (deg i)
/-- A regularity structure with graded basis `ι`: degrees `deg i` of the basis vectors and a
structure group `G ≤ GL(ι → ℝ)` of graded unipotent maps [Hai14, Definition 2.1]. -/
structure RegularityStructure (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The homogeneity `|e_i| = deg i` of the basis vector `e_i`. -/
  deg : ι → ℝ
  /-- The structure group. -/
  group : Subgroup (LinearMap.GeneralLinearGroup ℝ (ι → ℝ))
  isGradedUnipotent : ∀ g ∈ group, IsGradedUnipotent deg (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

end RegularityStructures
end
public section
namespace RegularityStructures
variable {ι : Type*} [DecidableEq ι] {deg : ι → ℝ}

namespace IsGradedUnipotent
variable {Γ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

end IsGradedUnipotent

namespace RegularityStructure
variable [Fintype ι] (𝒯 : RegularityStructure ι)

end RegularityStructure
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Semigroup.Basic ====
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
# Regularising semigroups and the distributions they see

A *regularising semigroup* on a measure space `(E, μ)` is a family of integral kernels
`Q_t(x, y)`, `t > 0`, with the semigroup property `∫ Q_s(x, z) Q_t(z, y) dz = Q_{s+t}(x, y)` and
the moment bounds `∫ |Q_t(x, y)| d(y, x)^r dy ≤ M_r t^{r/ℓ}`, where `d` is a distance-like size
and `ℓ > 0` the scaling order. This is the setting of [Hos25, Definition 2.6] (properties (i) and
(iii), with the condition (2.2) on `G` integrated against the kernel), specialised to the
unweighted case `w = 1`. The time-derivative bound (iv) of [Hos25] is not part of the interface;
the reconstruction theorem in the representation used here does not need it.

A *`Q`-distribution* is a family `(Λ_t)_{t>0}` of functions on `E` with
`∫ Q_s(x, y) Λ_t(y) dy = Λ_{s+t}(x)`: it records the regularisations `Λ_t = Q_t Λ` of a
distribution `Λ`. A tempered distribution `ξ` gives the family `Λ_t(x) = ⟨ξ, Q_t(x, ·)⟩`, and the
family determines `ξ` because `Q_t φ → φ` for test functions `φ`; for the Besov space
`B^{α,Q}_{∞,∞}` of [Hos25, Definition 2.9] this identification is (2.5) there. Working with the
families directly avoids completions: the reconstruction `Rf` is *defined* as the family
`t ↦ lim_{s↓0} R^t_s f` of [Hos25, proof of Theorem 4.1].

Source: [Hos25] = arXiv:2310.07396v2, §2.3 and §4.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
/-- A regularising semigroup on `(E, μ)`: kernels `Q_t(x, y)` with the semigroup property and
moment bounds `∫ |Q_t(x, y)| d(y, x)^r dμ(y) ≤ M_r t^{r/ℓ}` for every `r ≥ 0` and `t > 0`
([Hos25, Definition 2.6 (i), (iii) and (2.2)], unweighted). -/
structure RegularisingSemigroup (E : Type*) [MeasurableSpace E] (μ : Measure E) where
  /-- The kernel `Q_t(x, y)`. -/
  kernel : ℝ → E → E → ℝ
  /-- The scaling order `ℓ`: regularity `α` corresponds to the size `t^{α/ℓ}`. -/
  order : ℝ
  order_pos : 0 < order
  /-- The size `d(y, x)` of the increment from `x` to `y` (on `ℝ⁴`, the parabolic size
  `‖y - x‖_𝔰`). -/
  scaleDist : E → E → ℝ
  scaleDist_nonneg : ∀ x y, 0 ≤ scaleDist x y
  /-- The moment constants `M_r`. -/
  momentConst : ℝ → ℝ
  momentConst_nonneg : ∀ r, 0 ≤ momentConst r
  measurable_kernel : ∀ t, Measurable (Function.uncurry (kernel t))
  integrable_moment : ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x,
    Integrable (fun y => |kernel t x y| * scaleDist y x ^ r) μ
  moment_le : ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x,
    ∫ y, |kernel t x y| * scaleDist y x ^ r ∂μ ≤ momentConst r * t ^ (r / order)
  /-- The semigroup property `Q_s Q_t = Q_{s+t}`. -/
  semigroup : ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x y,
    ∫ z, kernel s x z * kernel t z y ∂μ = kernel (s + t) x y
namespace RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
/-- The action `(Q_t g)(x) = ∫ Q_t(x, y) g(y) dμ(y)` of the semigroup on functions. -/
def apply (t : ℝ) (g : E → ℝ) (x : E) : ℝ := ∫ y, K.kernel t x y * g y ∂μ
/-- The `Q`-distributions: families `(Λ_t)_{t>0}` of functions with `Q_s Λ_t = Λ_{s+t}`, the
integrals converging absolutely, normalised by `Λ_t = 0` for `t ≤ 0`. `Λ t x` is the
regularisation `(Q_t Λ)(x)` of the distribution `Λ`. -/
def distributions : Submodule ℝ (ℝ → E → ℝ) where
  carrier := {Λ | (∀ ⦃t : ℝ⦄, t ≤ 0 → Λ t = 0) ∧
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x,
      Integrable (fun y => K.kernel s x y * Λ t y) μ ∧ K.apply s (Λ t) x = Λ (s + t) x}
  add_mem' := by
    rintro Λ Λ' ⟨h0, h⟩ ⟨h0', h'⟩
    refine ⟨fun t ht => by simp [h0 ht, h0' ht], fun s t hs ht x => ?_⟩
    obtain ⟨hi, he⟩ := h hs ht x
    obtain ⟨hi', he'⟩ := h' hs ht x
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, mul_add]
      exact hi.add hi'
    simp only [apply, Pi.add_apply, mul_add] at he he' ⊢
    rw [integral_add hi hi', he, he']
  zero_mem' := ⟨fun _ _ => rfl, fun s t _ _ x => by simp [apply]⟩
  smul_mem' := by
    rintro c Λ ⟨h0, h⟩
    refine ⟨fun t ht => by simp [h0 ht], fun s t hs ht x => ?_⟩
    obtain ⟨hi, he⟩ := h hs ht x
    refine ⟨by simpa [mul_left_comm] using hi.const_mul c, ?_⟩
    simp only [apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c] at he ⊢
    rw [integral_const_mul, he]
end RegularisingSemigroup
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures.RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

end RegularityStructures.RegularisingSemigroup
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Model ====
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
# Models

A model `(Π, Γ)` for a regularity structure `𝒯` on a space `E` [Hai14, Definition 2.17],
[Hos25, Definition 3.2] consists of

* linear maps `Π_x : T → 𝒟'`, here `T →ₗ[ℝ] K.distributions`: a distribution is recorded through
  its regularisations `(Q_t Π_x τ)(z)` by the regularising semigroup `K` (see
  the design notes of the `Abstract` library);
* structure-group elements `Γ_{xy} ∈ G` with `Π_x Γ_{xy} = Π_y`, `Γ_{xx} = 1`,
  `Γ_{xy} Γ_{yz} = Γ_{xz}`.

We also require the regularisations `z ↦ (Q_t Π_x e_i)(z)` and the diagonal
`x ↦ (Q_t Π_x e_i)(x)` to be measurable (for models of interest both are continuous).

The analytic bounds are predicates with explicit constants, on a set `S ⊆ E`:

* `PiBoundOn γ C S`: `|(Q_t Π_x e_i)(x)| ≤ C t^{deg i/ℓ}` for `deg i < γ`, `0 < t ≤ 1`,
  `x ∈ S` ([Hos25, Definition 3.2 (2)], `p = ∞`, `w = 1`);
* `GammaBoundOn γ C S`: `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i − deg j}` for
  `deg j < deg i < γ`, `x, y ∈ S` ([Hai14, (2.15)]).

The norms `piNormOn`, `gammaNormOn` are the best constants (in `ℝ≥0∞`); `piNormOn_le_iff` and
`gammaNormOn_le_iff` characterise them. With `S` compact these are the local model norms of
[Hai14, Definition 2.17]; with `S = univ` the global norms of [Hos25].

Sources: [Hai14] = arXiv:1303.5113v4; [Hos25] = arXiv:2310.07396v2.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}
/-- A model `(Π, Γ)` for `𝒯` on `E`, with distributions represented through `K`
[Hai14, Definition 2.17]. -/
structure Model (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ) where
  /-- `Π_x : T → 𝒟'`. -/
  pi : E → (ι → ℝ) →ₗ[ℝ] K.distributions
  /-- `Γ_{xy} ∈ G`. -/
  gamma : E → E → 𝒯.group
  pi_gamma : ∀ x y τ,
    pi x (((gamma x y : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) τ) =
      pi y τ
  gamma_self : ∀ x, gamma x x = 1
  gamma_mul : ∀ x y z, gamma x y * gamma y z = gamma x z
  measurable_diag : ∀ i ⦃t : ℝ⦄, 0 < t →
    Measurable fun x => (pi x (Pi.single i 1) : ℝ → E → ℝ) t x
  measurable_pi : ∀ x i ⦃t : ℝ⦄, 0 < t → Measurable ((pi x (Pi.single i 1) : ℝ → E → ℝ) t)
namespace Model
variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
/-- `Γ_{xy}` as a linear map of `T`. -/
def gammaMap (M : Model 𝒯 K) (x y : E) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  ((M.gamma x y : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
/-- `(Q_t Π_x τ)(z)`: the regularisation of the distribution `Π_x τ`. -/
def regPi (M : Model 𝒯 K) (x : E) (τ : ι → ℝ) (t : ℝ) (z : E) : ℝ :=
  (M.pi x τ : ℝ → E → ℝ) t z
/-- The bound `|(Q_t Π_x e_i)(x)| ≤ C t^{deg i/ℓ}` for `deg i < γ`, `0 < t ≤ 1`, `x ∈ S`. -/
def PiBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
    |M.regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / K.order)

end Model
end RegularityStructures
end
public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}
namespace Model
variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

end Model
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Semigroup.Pairing.Basic ====
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
# Pairing of a `Q`-distribution with a test function: definitions

A `Q`-distribution `Λ` (a family `Λ_t = Q_t Λ`, see
`RegularityStructures.Analysis.Semigroup.Basic`) is paired with a
function `φ` by `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ dμ`.

* `pairing`: this limit (`limUnder`; when the limit does not exist the value is an unspecified
  junk value chosen by `Classical.epsilon`, so every use must come with a convergence statement);
* `IsGeneratorPair φ ψ`: `ψ = Lφ` in integrated form, `Q_h φ - φ = ∫_0^h Q_v ψ dv`;
* `IsSymmetric`, `IsMetricScale`: symmetry of the kernel, and `scaleDist` being a metric-like size;
* `IsLocalOrder Λ x₀ γ A C`: `Λ` is "of order `γ` at `x₀`", the hypothesis on
  `Rf - Π_{x₀} f(x₀)` in the reconstruction bound [Hai14, Theorem 3.10, (3.3)];
* `pairingConst A`, the constant in the bound `|⟨Λ, φ^λ_{x₀}⟩| ≲ λ^γ`.

Source: [Hai14] = arXiv:1303.5113v4.
-/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RegularityStructures.RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
/-- `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ dμ`. The semigroup `K` only fixes the measure `μ`. -/
def pairing (_K : RegularisingSemigroup E μ) (Λ : ℝ → E → ℝ) (φ : E → ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun s => ∫ y, Λ s y * φ y ∂μ

end RegularityStructures.RegularisingSemigroup
end
public section
open MeasureTheory Filter
open scoped Topology
namespace RegularityStructures.RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

end RegularityStructures.RegularisingSemigroup
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Parabolic.Basic ====
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
# Parabolic geometry on `ℝ⁴ = ℝ × ℝ³`

Space-time `ℝ⁴` is the product `ℝ × (Fin 3 → ℝ)`, a time coordinate and three space coordinates,
with the parabolic scaling `𝔰 = (2, 1, 1, 1)`. We measure distances with the parabolic size
`‖z‖_𝔰 = |z₀|^{1/2} + |z₁| + |z₂| + |z₃|` of [Hos25, §2.1] (`‖x‖_s = ∑ᵢ |xᵢ|^{1/sᵢ}`), which is
comparable to Hairer's `|z|_𝔰 = |z₀|^{1/2} + |z'|` [Hai14, §2], and satisfies the triangle
inequality and exact scaling `‖(c² t, c x)‖_𝔰 = c ‖(t, x)‖_𝔰`.

Sources: [Hos25] = arXiv:2310.07396v2, §2.1; [Hai14] = arXiv:1303.5113v4, §2.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- Space-time `ℝ⁴ = ℝ × ℝ³`, with time first. -/
abbrev ParabolicSpace : Type := ℝ × (Fin 3 → ℝ)
/-- The parabolic size `‖z‖_𝔰 = |z₀|^{1/2} + ∑ᵢ |zᵢ|` for the scaling `𝔰 = (2, 1, 1, 1)`. -/
def parabolicNorm (z : ParabolicSpace) : ℝ := Real.sqrt |z.1| + ∑ i, |z.2 i|
/-- The parabolic dilation `S^c z = (c² z₀, c z')`. -/
def parabolicDilate (c : ℝ) (z : ParabolicSpace) : ParabolicSpace := (c ^ 2 * z.1, c • z.2)
end RegularityStructures
end
public section
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.parabolicNorm_nonneg : ∀ (z : RegularityStructures.ParabolicSpace), 0 ≤ RegularityStructures.parabolicNorm z

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Parabolic.Generator ====
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
# The generator of the auxiliary parabolic semigroup

The auxiliary semigroup `Q_t` on `ℝ⁴` (`RegularityStructures.Analysis.Kernel.ParabolicSemigroup`)
has kernel `q_t(z) = g_t(z₀) ∏ᵢ k_t(zᵢ)` with `g_t = ∫ e^{-tξ²} cos(2πξ·) dξ` and
`k_t = ∫ e^{-tξ⁴} cos(2πξ·) dξ`, so `∂_t g_t = (4π²)⁻¹ ∂² g_t` and `∂_t k_t = -(16π⁴)⁻¹ ∂⁴ k_t`. Its
generator is

  `L φ = (4π²)⁻¹ ∂₀² φ − (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴ φ`,

an operator of parabolic order `ℓ = 4` (Hoshino arXiv:2310.07396v2, Example 2.7, with the
anisotropic `∑ᵢ ∂ᵢ⁴` in place of `Δ²`). Partial derivatives are taken as iterated Fréchet
derivatives along the coordinate directions `timeDir = (1, 0)` and `spaceDir i = (0, eᵢ)`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The time direction `(1, 0)` of `ℝ⁴`. -/
def timeDir : ParabolicSpace := (1, 0)
/-- The space direction `(0, eᵢ)` of `ℝ⁴`. -/
def spaceDir (i : Fin 3) : ParabolicSpace := (0, Pi.single i 1)

end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Kernel.Symbol ====
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
# One-dimensional kernels with symbol `exp(-t ξ^{2j})`

`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ` is the real, even inverse Fourier transform of
the symbol `ξ ↦ exp(-t ξ^{2j})`. For `j = 1` it is a Gaussian (the 1D heat kernel) and for `j = 2`
it is the quartic kernel of `∂_t + ∂_b⁴`. For `t > 0` it is the (real part of the) Schwartz
function `𝓕⁻ (exp(-t ξ^{2j}))`; we prove continuity, integrability, `∫ = 1`, the semigroup
property `k_s ⋆ k_t = k_{s+t}` and rapid decay of `k_1` and `k_1'`, using
`Mathlib.Analysis.Distribution.SchwartzSpace.Fourier` and `Mathlib.Analysis.Fourier.Convolution`.
This is the 1D building block of the auxiliary semigroup of [Hos25, Example 2.7]
(arXiv:2310.07396v2).
-/
@[expose] public noncomputable section
open MeasureTheory Real
namespace RegularityStructures
/-- The kernel with symbol `ξ ↦ exp(-t ξ^{2j})`:
`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ`. -/
def symKernel (j : ℕ) (t b : ℝ) : ℝ :=
  ∫ ξ, Real.exp (-(t * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b)
end RegularityStructures
end
public section
open MeasureTheory Real SchwartzMap
open scoped FourierTransform
namespace RegularityStructures
variable {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j)

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Kernel.Quartic ====
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
# The quartic kernel

`quarticKernel t b = symKernel 2 t b` is the inverse Fourier transform of `ξ ↦ exp(-t ξ^4)`,
`∫ exp(-t ξ^4) cos(2π ξ b) dξ`. It satisfies exact scaling with `t^{-1/4}`, has integral `1`,
the semigroup property and rapid decay of `quarticKernel 1` and its derivative, and the scaled moment
formula. See `RegularityStructures.Analysis.Kernel.Symbol` and
`RegularityStructures.Analysis.Kernel.SymbolScale` for the proofs. This is the
spatial factor of the auxiliary semigroup of [Hos25, Example 2.7] (arXiv:2310.07396v2).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The one-dimensional quartic kernel `𝓕⁻¹(ξ ↦ exp(-t ξ⁴))` (fundamental solution of `∂_t + ∂_b⁴`). -/
def quarticKernel (t b : ℝ) : ℝ := symKernel 2 t b
/-- The moment `∫ |quarticKernel 1 b| |b|^s db`. -/
def quarticMoment (s : ℝ) : ℝ := ∫ b, |quarticKernel 1 b| * |b| ^ s
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Kernel.Gaussian ====
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
# The one-dimensional heat kernel

`heatKernel1D t b = symKernel 1 t b` is the inverse Fourier transform of `ξ ↦ exp(-t ξ^2)`,
`∫ exp(-t ξ^2) cos(2π ξ b) dξ`. It satisfies exact scaling with `t^{-1/2}`, has integral `1`,
the semigroup property and rapid decay of `heatKernel1D 1` and its derivative, and the scaled moment
formula. See `RegularityStructures.Analysis.Kernel.Symbol` and
`RegularityStructures.Analysis.Kernel.SymbolScale` for the proofs. This is the
temporal factor of the auxiliary semigroup of [Hos25, Example 2.7] (arXiv:2310.07396v2).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The one-dimensional heat kernel `𝓕⁻¹(ξ ↦ exp(-t ξ²)) = √(π/t) exp(-π² a²/t)` (variance proportional to `t`). -/
def heatKernel1D (t b : ℝ) : ℝ := symKernel 1 t b
/-- The moment `∫ |heatKernel1D 1 b| |b|^s db`. -/
def heatMoment (s : ℝ) : ℝ := ∫ b, |heatKernel1D 1 b| * |b| ^ s
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Kernel.Parabolic ====
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
# The parabolic kernel on `ℝ × ℝ³`

`parabolicKernel t (s, x) = heatKernel1D t s * ∏ᵢ quarticKernel t (xᵢ)`: the tensor product of the
1D heat kernel in time and three 1D quartic kernels in space. It is the fundamental solution of
`∂_t - ∂₀² + ∑ᵢ ∂ᵢ⁴` ([Hos25, Example 2.7] (arXiv:2310.07396v2), with the spatial bi-Laplacian
replaced by `∑ᵢ ∂ᵢ⁴`), and is *only* used as the auxiliary kernel measuring regularity.

We prove joint measurability, exact parabolic scaling
`q_t(z) = t^{-5/4} q_1(S^{t^{-1/4}} z)`, `∫ q_t = 1`, and integrability and the value of the weighted
integrals `∫ |g_t(z₀)| |z₀|^a ∏ᵢ |k_t(zᵢ)| |zᵢ|^{eᵢ} dz`, from which the moment bounds follow
(`RegularityStructures.Analysis.Kernel.Moments`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The parabolic kernel `q_t(s, x) = g_t(s) ∏ᵢ k_t(xᵢ)`. -/
def parabolicKernel (t : ℝ) (z : ParabolicSpace) : ℝ :=
  heatKernel1D t z.1 * ∏ i, quarticKernel t (z.2 i)
/-- The weight `|g_t(z₀)| |z₀|^a ∏ᵢ |k_t(zᵢ)| |zᵢ|^{eᵢ}`. -/
def parabolicKernelWeight (t a : ℝ) (e : Fin 3 → ℝ) (z : ParabolicSpace) : ℝ :=
  (|heatKernel1D t z.1| * |z.1| ^ a) * ∏ i, (|quarticKernel t (z.2 i)| * |z.2 i| ^ e i)
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.parabolicKernel_neg : ∀ (t : ℝ) (z : RegularityStructures.ParabolicSpace),
  RegularityStructures.parabolicKernel t (-z) = RegularityStructures.parabolicKernel t z
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.measurable_parabolicKernel : ∀ (t : ℝ), Measurable (RegularityStructures.parabolicKernel t)

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Kernel.GeneratorKernel ====
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
# The heat equation for the parabolic kernel

`kernelDerivs t a b₀ b₁ b₂ (s, x) = g_t^{(a)}(s) k_t^{(b₀)}(x₀) k_t^{(b₁)}(x₁) k_t^{(b₂)}(x₂)`
are the partial derivatives of `parabolicKernel t = kernelDerivs t 0 0 0 0`. We show that
differentiating along `timeDir` raises `a`, and along `spaceDir i` raises `bᵢ`, and deduce the
pointwise heat equation `∂_t q_t = L q_t`, `L = (4π²)⁻¹ ∂₀² - (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴`
(`parabolicTimeDeriv_eq`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The directional derivative `D_d f = x ↦ f'(x) d`. -/
def dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : E) (f : E → ℝ) : E → ℝ :=
  fun x => fderiv ℝ f x d

end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Kernel.Moments ====
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
# Moment bounds for the parabolic kernel

For `t > 0` and `r ≥ 0`, `∫ |q_t(w)| ‖w‖_𝔰^r dw ≤ M_r t^{r/4}`, with the explicit constant
`M_r = 4^r (G_{r/2} K_0³ + 3 G_0 K_r K_0²)` where `G_s = ∫ |g_1(a)| |a|^s da` and
`K_s = ∫ |k_1(b)| |b|^s db`. The proof bounds `‖w‖_𝔰^r ≤ 4^r (|w₀|^{r/2} + ∑ᵢ |wᵢ|^r)` and evaluates
the resulting product integrals by Fubini (`RegularityStructures.Analysis.Kernel.Parabolic`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The moment constant `M_r = 4^r (G_{r/2} K_0³ + 3 G_0 K_r K_0²)` of the parabolic kernel. -/
def parabolicMomentConst (r : ℝ) : ℝ :=
  (4 : ℝ) ^ r * (heatMoment (r / 2) * quarticMoment 0 ^ 3 +
    3 * (heatMoment 0 * quarticMoment r * quarticMoment 0 ^ 2))
/-- The sum of the four weights bounding `|q_t(z)| ‖z‖^r`. -/
def parabolicMomentBound (t r : ℝ) (z : ParabolicSpace) : ℝ :=
  (4 : ℝ) ^ r * (parabolicKernelWeight t (r / 2) 0 z + parabolicKernelWeight t 0 (Pi.single 0 r) z +
    parabolicKernelWeight t 0 (Pi.single 1 r) z + parabolicKernelWeight t 0 (Pi.single 2 r) z)
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.parabolicMomentConst_nonneg : ∀ (r : ℝ), 0 ≤ RegularityStructures.parabolicMomentConst r

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.abs_parabolicKernel_mul_le : ∀ (t : ℝ) {r : ℝ},
  0 ≤ r →
    ∀ (z : RegularityStructures.ParabolicSpace),
      |RegularityStructures.parabolicKernel t z| * RegularityStructures.parabolicNorm z ^ r ≤
        RegularityStructures.parabolicMomentBound t r z
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.integrable_parabolicMomentBound : ∀ {t : ℝ},
  0 < t →
    ∀ {r : ℝ},
      0 ≤ r →
        MeasureTheory.Integrable (RegularityStructures.parabolicMomentBound t r)
          MeasureTheory.MeasureSpace.volume
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.integral_parabolicMomentBound : ∀ {t : ℝ},
  0 < t →
    ∀ {r : ℝ},
      0 ≤ r →
        ∫ (z : RegularityStructures.ParabolicSpace),
            RegularityStructures.parabolicMomentBound t r z =
          RegularityStructures.parabolicMomentConst r * t ^ (r / 4)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Kernel.ParabolicSemigroup ====
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
# The auxiliary regularising semigroup on `ℝ⁴`

`parabolicSemigroup` is the `RegularisingSemigroup ParabolicSpace volume` with kernel
`Q_t(x, y) = q_t(x - y)`, `q_t = parabolicKernel t`, scaling order `ℓ = 4` and size
`d(y, x) = ‖y - x‖_𝔰`. It is used *only* to measure regularity; it is not the causal heat kernel
of the PDE. This is the setting of [Hos25, Definition 2.6 (i), (iii), Example 2.7]
(arXiv:2310.07396v2).

* the semigroup property follows from the 1D ones by Fubini
  (`integral_quarticKernel_mul_quarticKernel`, `integral_heatKernel1D_mul_heatKernel1D`);
* the moment bounds from `RegularityStructures.Analysis.Kernel.Moments`.
-/
public section
open MeasureTheory
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.integral_parabolicKernel_mul_parabolicKernel : ∀ {s t : ℝ},
  0 < s →
    0 < t →
      ∀ (x y : RegularityStructures.ParabolicSpace),
        ∫ (z : RegularityStructures.ParabolicSpace),
            RegularityStructures.parabolicKernel s (x - z) *
              RegularityStructures.parabolicKernel t (z - y) =
          RegularityStructures.parabolicKernel (s + t) (x - y)
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.integrable_abs_parabolicKernel_mul_norm : ∀ {t : ℝ},
  0 < t →
    ∀ {r : ℝ},
      0 ≤ r →
        MeasureTheory.Integrable
          (fun (w : RegularityStructures.ParabolicSpace) ↦
            |RegularityStructures.parabolicKernel t w| * RegularityStructures.parabolicNorm w ^ r)
          MeasureTheory.MeasureSpace.volume
/-- The auxiliary regularising semigroup `Q_t(x, y) = q_t(x - y)` on `ℝ⁴ = ℝ × ℝ³`
with order `4`, where `q_t(s, x) = g_t(s) ∏ᵢ k_t(xᵢ)` is the tensor product of the 1D heat kernel
and three 1D quartic kernels. The moment constant is `parabolicMomentConst`. -/
@[expose] noncomputable def parabolicSemigroup : RegularisingSemigroup ParabolicSpace volume where
  kernel t x y := parabolicKernel t (x - y)
  order := 4
  order_pos := by norm_num
  scaleDist x y := parabolicNorm (x - y)
  scaleDist_nonneg x y := parabolicNorm_nonneg _
  momentConst := parabolicMomentConst
  momentConst_nonneg := parabolicMomentConst_nonneg
  measurable_kernel t :=
    (measurable_parabolicKernel t).comp (measurable_fst.sub measurable_snd)
  integrable_moment t ht r hr x := by
    have h : Integrable (fun y : ParabolicSpace => |parabolicKernel t (y - x)| *
        parabolicNorm (y - x) ^ r) volume := by
      have h0 := integrable_abs_parabolicKernel_mul_norm ht hr
      rw [Measure.volume_eq_prod] at h0 ⊢
      exact h0.comp_sub_right x
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [← parabolicKernel_neg t (y - x), neg_sub]
  moment_le t ht r hr x := by
    have e : ∀ y : ParabolicSpace, |parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ r =
        |parabolicKernel t (y - x)| * parabolicNorm (y - x) ^ r := fun y => by
      rw [← parabolicKernel_neg t (y - x), neg_sub]
    simp only [e]
    have hshift : ∫ y : ParabolicSpace, |parabolicKernel t (y - x)| * parabolicNorm (y - x) ^ r =
        ∫ w : ParabolicSpace, |parabolicKernel t w| * parabolicNorm w ^ r := by
      rw [Measure.volume_eq_prod]
      exact integral_sub_right_eq_self (fun w : ParabolicSpace =>
        |parabolicKernel t w| * parabolicNorm w ^ r) x
    rw [hshift]
    calc ∫ w, |parabolicKernel t w| * parabolicNorm w ^ r
        ≤ ∫ w, parabolicMomentBound t r w :=
          integral_mono (integrable_abs_parabolicKernel_mul_norm ht hr)
            (integrable_parabolicMomentBound ht hr) (fun w => abs_parabolicKernel_mul_le t hr w)
      _ = parabolicMomentConst r * t ^ (r / 4) := integral_parabolicMomentBound ht hr
      _ = _ := by norm_num
  semigroup s t hs ht x y := integral_parabolicKernel_mul_parabolicKernel hs ht x y
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.FixedPointTimeSlab ====
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
# Time slabs in parabolic space-time

The concrete slabs of [Hai14, §7.1] on `ℝ⁴ = ℝ × ℝ³`: `P = {t = 0}`, the distance to `P` for the
parabolic size `‖z‖_𝔰 = |z₀|^{1/2} + ∑ᵢ |zᵢ|` is `timeZeroDist z = |z₀|^{1/2}`
(`timeZeroDist_le_parabolicNorm_sub`, `exists_parabolicNorm_sub_eq_timeZeroDist`), and the slab
`(0, T] × ℝ³` is `timeSlab T`.

These discharge the slab hypotheses of the abstract fixed-point theorems with `𝔰₀ = 2`:

* `timeZeroDist_le_rpow_of_mem_timeSlab`: `ρ ≤ T^{1/2}` on the slab (the short-time gain is
  `T^{κ/2}`);
* `timeSlab_mono`, `timeSlab_zero`: the slabs increase and `S_0 = ∅`;
* `measurableSet_timeSlab_pos`: measurability of `S_T⁺ = S_T ∩ {ρ > 0}`.

Source: [Hai14] = arXiv:1303.5113v4, §7.1 (`P = {(t, x) : t = 0}`, `O_T`).
-/
@[expose] public noncomputable section
namespace RegularityStructures

/-- The time slab `(0, T] × ℝ³`. -/
def timeSlab (T : ℝ) : Set ParabolicSpace := {z | 0 < z.1 ∧ z.1 ≤ T}
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Singular.Window.Basic ====
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
# Hairer's time window and window model bounds

`hairerTimeWindow = {z | -1 ≤ z.1 ≤ 2}` is the window `O = [-1, 2] × ℝ³` of [Hai14, Thm 7.1].
If `z` has time coordinate in `[0, 1]` (in particular for `z` in the slab `(0, T]`, `T ≤ 1`),
the whole closed parabolic ball `{y | ‖y - z‖_𝔰 ≤ 1}` lies in the window
(`ball_subset_hairerTimeWindow`). The convenience lemma `abs_gammaMap_single_le_of_window` is the
bound `|(Γ_{yx} e_i)_j| ≤ C_Γ d(y, x)^{deg i - deg j}` for `x, y` in the window.

`Model.HasQualitativeGrowth M γ` is the purely qualitative polynomial growth of the
regularisations `Q_t Π_x e_i` (for `deg i < γ`, `0 < t ≤ 1`); the constants are never used
quantitatively, only for the existence of pairings.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.1, (2.15).
-/
@[expose] public section
namespace RegularityStructures
/-- Hairer's window `O = [-1, 2] × ℝ³` of [Hai14, Theorem 7.1]. -/
def hairerTimeWindow : Set ParabolicSpace := {z | -1 ≤ z.1 ∧ z.1 ≤ 2}
end RegularityStructures
end
public section
open Set
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.ModelNear ====
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
# Near-pair `Γ`-bounds

`GammaBoundNearOn γ C R S` is the `Γ`-bound of `Model.GammaBoundOn` restricted to pairs of points
of `S` at scaled distance at most `R`:

  `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i − deg j}`,  `deg j < deg i < γ`,  `x, y ∈ S`,
  `d(y, x) ≤ R`.

Hairer's model norm only uses `R = 1` ([Hai14, (2.17)]).  The far-pair version does not follow from
the near one with a polynomial constant (see `ModelNearChain`).  `GammaDiffBoundNearOn` is the
corresponding bound for the difference of two models.

Source: [Hai14] = arXiv:1303.5113v4, Definition 2.17.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}
/-- The radius of the near-pair `Γ`-hypotheses of the window chain. -/
def gammaNearRadius : ℝ := 4

namespace Model
variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
/-- The bound `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i − deg j}` for `deg j < deg i < γ`, `x, y ∈ S`
with `d(y, x) ≤ R` (near pairs only). -/
def GammaBoundNearOn (M : Model 𝒯 K) (γ C R : ℝ) (S : Set E) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x ∈ S, ∀ y ∈ S, K.scaleDist y x ≤ R →
    |M.gammaMap y x (Pi.single i 1) j| ≤ C * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

variable {M M₁ M₂ : Model 𝒯 K} {γ C R : ℝ} {S : Set E}

/-- The `Γ`-bound of the window chain: near pairs of radius `gammaNearRadius`. -/
def GammaNearOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  M.GammaBoundNearOn γ C gammaNearRadius S

end Model
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Parabolic.Polynomial ====
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
# Parabolically weighted polynomials on `ℝ × ℝ³`

Polynomials in the four coordinates `(z₀, z₁, z₂, z₃)` of `ParabolicSpace`, graded by the parabolic
weights `𝔰 = (2, 1, 1, 1)`. A weighted homogeneous polynomial of degree `n` scales like `c ^ n`
under `parabolicDilate c`, and a monomial of degree `n` is bounded by `‖z‖_𝔰 ^ n`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The parabolic weights `𝔰 = (2, 1, 1, 1)`. -/
def parabolicWeight : Fin 4 → ℕ := ![2, 1, 1, 1]
/-- The four coordinates `(z₀, z₁, z₂, z₃)` of a point of parabolic space. -/
def parabolicCoords (z : ParabolicSpace) : Fin 4 → ℝ := ![z.1, z.2 0, z.2 1, z.2 2]
/-- Evaluation of a polynomial in four variables at a point of parabolic space. -/
def evalParabolic (p : MvPolynomial (Fin 4) ℝ) (z : ParabolicSpace) : ℝ :=
  MvPolynomial.eval (parabolicCoords z) p
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Polynomial.Basic ====
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
# The polynomial regularity structure: model space

The model space of the polynomial regularity structure `T̄_N` on `ℝ⁴` with parabolic scaling
[Hai14, Section 2.2, Remark 2.23] has the basis `X^k`, for the multi-indices `k` of parabolic degree
`|k|_𝔰 = 2 k₀ + k₁ + k₂ + k₃ < N`, with `deg X^k = |k|_𝔰`. Here `PolyIndex N` is the type of these
multi-indices, `toPoly` identifies `PolyIndex N → ℝ` with polynomials in four variables, and
`ofPoly` reads off coefficients.

Source: [Hai14] = arXiv:1303.5113v4.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The multi-indices `k` of parabolic degree `|k|_𝔰 < N`: the basis of the polynomial
regularity structure. -/
abbrev PolyIndex (N : ℕ) : Type := {k : Fin 4 →₀ ℕ // Finsupp.weight parabolicWeight k < N}
/-- The homogeneity `|X^k|_𝔰 = 2 k₀ + k₁ + k₂ + k₃` of the basis vector `X^k`. -/
def polyDeg (N : ℕ) : PolyIndex N → ℝ := fun k => (Finsupp.weight parabolicWeight k.1 : ℝ)
end RegularityStructures
end
public section
namespace RegularityStructures
variable {N : ℕ}

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.finite_polyIndex : ∀ (N : ℕ), Finite (RegularityStructures.PolyIndex N)
noncomputable instance (N : ℕ) : Fintype (PolyIndex N) :=
  haveI := finite_polyIndex N
  Fintype.ofFinite _
end RegularityStructures
end
@[expose] public noncomputable section
namespace RegularityStructures
variable {N : ℕ}
/-- The polynomial `∑ τ_k X^k` with coefficient vector `τ`. -/
def toPoly (N : ℕ) : (PolyIndex N → ℝ) →ₗ[ℝ] MvPolynomial (Fin 4) ℝ where
  toFun τ := ∑ k, τ k • MvPolynomial.monomial k.1 (1 : ℝ)
  map_add' τ σ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c τ := by simp [Finset.smul_sum, mul_smul]

end RegularityStructures
end
public section
namespace RegularityStructures
variable {N : ℕ}

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Polynomial.Structure ====
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
# The polynomial regularity structure `T̄_N`

The structure group `polyGroup N` is the group of translations `Γ_h : X^k ↦ (X + h)^k`, `h ∈ ℝ⁴`,
and `polynomialStructure N` is the regularity structure with basis `X^k`, `|k|_𝔰 < N`, degrees
`|k|_𝔰` and this group [Hai14, Section 2.2, Remark 2.23, (2.20)-(2.21)].
-/
@[expose] public noncomputable section
namespace RegularityStructures
variable {N : ℕ}

/-- The polynomial model `Π_x τ (z) = (z - x)^τ` at the level of functions. -/
def polyEval (x : ParabolicSpace) (τ : PolyIndex N → ℝ) (z : ParabolicSpace) : ℝ :=
  MvPolynomial.eval (parabolicCoords (z - x)) (toPoly N τ)
end RegularityStructures
end
public section
namespace RegularityStructures
variable {N : ℕ}

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Integration ====
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
# Sectors, abstract polynomials and abstract integration maps

The algebraic layer of [Hai14, §5] in the graded-basis representation:

* `homogeneousProj deg α`: the projection `Q_α : T → T_α`;
* `RegularityStructure.IsSector V`: `V` is graded (`Q_α V ⊂ V` for all `α`) and `G`-invariant
  [Hai14, Definition 2.5] (complements exist automatically in finite dimension); the regularity
  condition `V_β = 0` for `β < α` is `IsSector.OfRegularity`;
* `PolynomialSector 𝒯 N`: an embedding of the abstract polynomials `X^k`, `|k|_𝔰 < N`, into the
  basis of `𝒯`, preserving degrees, whose span `T̄` is `G`-invariant [Hai14, §5, before
  Assumption 5.3];
* `IsAbstractIntegration P V I β`: `I : T → T` is an abstract integration map of order `β` on the
  sector `V` [Hai14, Definition 5.7]: `I (V ∩ T_α) ⊂ T_{α+β}`, `I = 0` on `V ∩ T̄`, and
  `IΓa − ΓIa ∈ T̄` for `a ∈ V`, `Γ ∈ G`.

Source: [Hai14] = arXiv:1303.5113v4, Definitions 2.5 and 5.7.
-/
@[expose] public noncomputable section
namespace RegularityStructures
variable {ι : Type*}
/-- The projection `Q_α : T → T_α` onto the homogeneous component of degree `α`. -/
def homogeneousProj (deg : ι → ℝ) (α : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun τ i := if deg i = α then τ i else 0
  map_add' τ σ := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c τ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp
variable [Fintype ι] [DecidableEq ι]
namespace RegularityStructure
/-- A sector [Hai14, Definition 2.5]: a graded, `G`-invariant subspace of `T`. -/
structure IsSector (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) : Prop where
  graded : ∀ α, ∀ a ∈ V, homogeneousProj 𝒯.deg α a ∈ V
  invariant : ∀ g ∈ 𝒯.group, ∀ a ∈ V,
    ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a ∈ V

end RegularityStructure
/-- The abstract polynomials `X^k`, `|k|_𝔰 < N`, inside a regularity structure on `ℝ⁴`: an
injective, degree-preserving embedding of `PolyIndex N` into the basis whose span `T̄` is
invariant under the structure group. -/
structure PolynomialSector (𝒯 : RegularityStructure ι) (N : ℕ) where
  /-- The basis index of `X^k`. -/
  emb : PolyIndex N → ι
  emb_injective : Function.Injective emb
  deg_emb : ∀ k, 𝒯.deg (emb k) = polyDeg N k
  invariant : ∀ g ∈ 𝒯.group, ∀ τ : ι → ℝ, (∀ i, i ∉ Set.range emb → τ i = 0) →
    ∀ i, i ∉ Set.range emb →
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) τ i = 0
namespace PolynomialSector
variable {𝒯 : RegularityStructure ι} {N : ℕ}
/-- The span `T̄` of the abstract polynomials. -/
def subspace (P : PolynomialSector 𝒯 N) : Submodule ℝ (ι → ℝ) where
  carrier := {τ | ∀ i, i ∉ Set.range P.emb → τ i = 0}
  add_mem' {τ σ} hτ hσ i hi := by simp [hτ i hi, hσ i hi]
  zero_mem' _ _ := rfl
  smul_mem' c τ hτ i hi := by simp [hτ i hi]
end PolynomialSector
/-- An abstract integration map of order `β` on the sector `V` [Hai14, Definition 5.7]. -/
structure IsAbstractIntegration {𝒯 : RegularityStructure ι} {N : ℕ}
    (P : PolynomialSector 𝒯 N) (V : Submodule ℝ (ι → ℝ)) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (β : ℝ) : Prop where
  pos : 0 < β
  map_homogeneous : ∀ α, ∀ a ∈ V, a ∈ homogeneousSubspace 𝒯.deg α →
    I a ∈ homogeneousSubspace 𝒯.deg (α + β)
  map_poly : ∀ a ∈ V, a ∈ P.subspace → I a = 0
  comm : ∀ g ∈ 𝒯.group, ∀ a ∈ V,
    I (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a) -
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (I a) ∈ P.subspace
end RegularityStructures
end
public section
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.PolyGrowth.Reconstruction ====
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
# The reconstruction theorem for models of polynomial growth

Stationary random models are not globally bounded: `sup_x |(Q_t Π_x e_i)(x)| = ∞`. They satisfy
the weighted bound `|(Q_t Π_x e_i)(x)| ≤ C_Π ρ(x) t^{deg i/ℓ}` for a polynomially moderate weight
`ρ ≥ 1` (`ρ(z) ≤ ρ(y)(1 + d(z, y))^p`), as in [Hos25, Definition 3.2] with weight `w = 1/ρ`.
For such a model and `f ∈ D^γ` (`γ > 0`) the reconstruction `Rf` exists, is unique, and
`|(Q_t (Rf − Π_x f(x)))(x)| ≤ c C_Π C_f ρ(x) t^{γ/ℓ}` (`Model.abs_reconstruct_sub_le_growth`),
with `c` depending only on `𝒯`, `K`, `p` and `γ`. Here only the model is weighted; for
stationary random models the modelled distributions must be weighted too, which is done in
the weighted multilevel Schauder estimate
(`RegularityStructures.Abstract.Integration.Growth`).

Source: [Hos25] = arXiv:2310.07396v2, Definitions 2.1, 3.2 and Theorem 4.1.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}
namespace Model
variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
/-- The weighted model bound `|(Q_t Π_x e_i)(x)| ≤ C ρ(x) t^{deg i/ℓ}` for `deg i < γ`,
`0 < t ≤ 1`. -/
def PiBoundGrowth (M : Model 𝒯 K) (γ C : ℝ) (ρ : E → ℝ) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
    |M.regPi x (Pi.single i 1) t x| ≤ C * ρ x * t ^ (𝒯.deg i / K.order)
end Model
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}
namespace Model
variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

end Model
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Semigroup.Weighted.Defs ====
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
# Weights, weighted germs and weighted coherence

Weighted germs and weighted coherence, following [Hos25, Definitions 2.1, 3.2, 3.5] with `p = ∞`. We
write the weight as a growth function `ρ = 1 / w ≥ 1`; polynomial moderateness
`ρ z ≤ ρ y (1 + d(z, y))^p` replaces the condition `w(x + y) ≤ w*(x) w(y)`. Stationary random models
have `sup_x |(Q_t Π_x τ)(x)| = ∞` but are bounded by `ρ(x) t^{deg/ℓ}` for a polynomial `ρ`, which is
why the reconstruction must allow growth.

* `IsModerateWeight ρ p`: `ρ ≥ 1` measurable, `ρ z ≤ ρ y (1 + d(z, y))^p`;
* `IsWeightedGerm F ρ`, `IsWeightedCoherent F ρ γ A C`: weighted versions of `IsGerm`,
  `IsCoherent` (the case `ρ = 1`, `p = 0` is the unweighted one);
* `weightConst`, `weightedCoherenceConst`, `weightedReconstructionConst`: explicit constants;
* `IsModerateWeight.le_mul`: `ρ z ≤ ρ y 2^p (1 + d(z, y)^p)`, the form used with the moments.

Source: [Hos25] = arXiv:2310.07396v2, Theorem 4.1.
-/
@[expose] public noncomputable section
open MeasureTheory Filter Set
namespace RegularityStructures.RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
/-- A polynomially moderate weight: `ρ ≥ 1` measurable, `ρ z ≤ ρ y * (1 + d(z, y))^p`. -/
structure IsModerateWeight (ρ : E → ℝ) (p : ℝ) : Prop where
  one_le : ∀ x, 1 ≤ ρ x
  measurable : Measurable ρ
  nonneg_exp : 0 ≤ p
  le : ∀ y z, ρ z ≤ ρ y * (1 + K.scaleDist z y) ^ p

end RegularityStructures.RegularisingSemigroup
end
public section
open MeasureTheory Filter Set
namespace RegularityStructures.RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

variable {K}

variable (K)

end RegularityStructures.RegularisingSemigroup
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Integration.Growth.Setting ====
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
# The weighted hypotheses of the multilevel Schauder estimate

For stationary random models only weighted bounds hold. We use polynomially moderate weights
`ρ ≥ 1` (`IsModerateWeight ρ p`: `ρ z ≤ ρ y (1 + d(z, y))^p`) and the bounds

* `Model.PiBoundGrowth γ C ρP`: `|(Q_t Π_x e_i)(x)| ≤ C ρP(x) t^{deg i/ℓ}`;
* `Model.GammaBoundGrowth γ C ρG q`:
  `|(Γ_{yx} e_i)_j| ≤ C ρG(x) (1 + d(y, x))^q d(y, x)^{deg i − deg j}` for `deg j < deg i < γ`.

`Model.GrowthModel` bundles these bounds for a model `M`, with weights `ρP, ρG` moderate with the
same exponent `p`. The assumptions that do not involve the weights (`IsRealising`,
`IsAbstractIntegration`, degree conditions) are kept separate.

Source: [Hos25] = arXiv:2310.07396v2, Definitions 3.2, 3.5; [Hai14] = arXiv:1303.5113v4, §5.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}
namespace Model
variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
/-- The weighted structure-group bound `|(Γ_{yx} e_i)_j| ≤ C ρG(x) (1 + d(y, x))^q d(y, x)^{deg i − deg j}`
for `deg j < deg i < γ`. -/
def GammaBoundGrowth (M : Model 𝒯 K) (γ C : ℝ) (ρ : E → ℝ) (q : ℝ) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
    |M.gammaMap y x (Pi.single i 1) j| ≤
      C * ρ x * (1 + K.scaleDist y x) ^ q * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)
/-- The standing weighted hypotheses on a model `M`: `γ > 0`, moderate weights `ρP, ρG` with
exponent `p`, and the bounds `PiBoundGrowth`, `GammaBoundGrowth` (with growth exponent `qG ≥ 0`). -/
structure GrowthModel (M : Model 𝒯 K) (γ CPi CGam : ℝ) (ρP ρG : E → ℝ) (p qG : ℝ) : Prop where
  pos : 0 < γ
  moderateP : K.IsModerateWeight ρP p
  moderateG : K.IsModerateWeight ρG p
  nonnegG : 0 ≤ qG
  piBound : M.PiBoundGrowth γ CPi ρP
  gammaBound : M.GammaBoundGrowth γ CGam ρG qG
  piBound_nonneg : 0 ≤ CPi
end Model
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Parabolic.SingularKernel ====
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
# Regularising kernels on `ℝ⁴` (Hairer's Assumption 5.1)

A kernel `K(x, y)` "improves regularity by `β`" [Hai14, Assumption 5.1] if it decomposes as
`K = ∑_{n ≥ 0} K_n` with

* `K_n` smooth and supported in `{‖x − y‖_𝔰 ≤ 2^{-n}}`;
* `|D₁^k D₂^l K_n(x, y)| ≤ C 2^{(|𝔰| − β + |l|_𝔰 + |k|_𝔰) n}`, `|𝔰| = 5` ((5.4));
* `|∫ (x − y)^l D₂^k K_n(x, y) dx| ≤ C 2^{-βn}` and `|∫ (y − x)^l D₁^k K_n(x, y) dy| ≤ C 2^{-βn}`
  ((5.5));

and it annihilates polynomials up to order `r` if `∫ K_n(x, y) P(y) dy = 0` for all polynomials
`P` of parabolic degree `≤ r` [Hai14, Assumption 5.4].

Derivatives along a multi-index `k ∈ ℕ⁴` are iterated Fréchet derivatives along the coordinate
directions (`multiDirs k`, `k₀` copies of the time direction and `kᵢ` copies of the `i`-th space
direction); `D₁` and `D₂` act on the first and second argument of `K_n` respectively.

Source: [Hai14] = arXiv:1303.5113v4, §5.1, (5.3)–(5.6).
-/
@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures
/-- The coordinate directions of `ℝ⁴`: `0 ↦ (1, 0)`, `i + 1 ↦ (0, eᵢ)`. -/
def coordDir : Fin 4 → ParabolicSpace :=
  Fin.cases timeDir spaceDir
/-- The list of directions of the multi-index `k`: `k_j` copies of `coordDir j`. -/
def multiDirs (k : Fin 4 →₀ ℕ) : List ParabolicSpace :=
  (Finsupp.toMultiset k).toList.map coordDir
/-- The parabolic degree `|k|_𝔰 = 2k₀ + k₁ + k₂ + k₃` of a multi-index. -/
def multiDeg (k : Fin 4 →₀ ℕ) : ℕ := Finsupp.weight parabolicWeight k
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Heat.Decomposition.LineIter ====
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
# Iterated directional derivatives along a list of directions

`lineIter [d₁, …, dₙ] f = D_{d₁} ⋯ D_{dₙ} f`, where `D_d f = x ↦ f'(x) d` (`dirDeriv`).  For smooth
`f` this agrees with `iteratedFDeriv ℝ n f w (fun i => L.get i)`, and it interacts simply with
composition by continuous linear maps, sign changes and scalar rescalings of the directions.
-/
@[expose] public noncomputable section
open scoped ContDiff
namespace RegularityStructures
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- `lineIter [d₁, …, dₙ] f = D_{d₁} ⋯ D_{dₙ} f`. -/
def lineIter : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | d :: L, f => dirDeriv d (lineIter L f)
end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Heat.Decomposition.Vanishing ====
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
# Vanishing of moments by integration by parts

If `J` is a list of coordinate indices in which some index `i` occurs more often than the exponent
`l i` of the monomial `z^l`, then `∫ z^l D_J g = 0` for every smooth compactly supported `g`.
Integrating by parts removes one derivative at a time and differentiates the monomial.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The monomial `z ↦ ∏ᵢ zᵢ^{lᵢ}` in the four parabolic coordinates. -/
def monoFn (l : Fin 4 → ℕ) (z : ParabolicSpace) : ℝ := ∏ i, parabolicCoords z i ^ l i
end RegularityStructures
end
public section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Heat.Annihilating.Scaled ====
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
# Dyadic rescalings of a bump

For `h : ℝ⁴ → ℝ` we set `scaledShell h n z = (2^n)^3 h(S^{2^n} z)` (`S^c = parabolicDilate c`).
If `h` is smooth and supported in the unit parabolic ball, then `scaledShell h n` is smooth and
supported in `‖z‖_𝔰 ≤ 2^{-n}`, its derivatives obey the exact scaling
`D_J (scaledShell h n) = (2^n)^{3 + |J|_𝔰} (D_J h)(S^{2^n} ·)`, and its moments scale exactly.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The `n`-th dyadic rescaling `z ↦ (2^n)^3 h(S^{2^n} z)` of `h`. -/
def scaledShell (h : ParabolicSpace → ℝ) (n : ℕ) (z : ParabolicSpace) : ℝ :=
  ((2 : ℝ) ^ n) ^ 3 * h (parabolicDilate (2 ^ n) z)
end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Profile.Basic ====
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
# Kernel profiles for the shells `K_n = scaledShell h n`

The multilevel Schauder machinery of `RegularityStructures.Abstract.Integration` is stated for the
particular decomposition `K_n = annShell N n = scaledShell (annKernel0 N) n` of [Hai14, Lemma 5.5].
Only three properties of the profile `annKernel0 N` are used: it is smooth, supported in the closed
unit parabolic ball, and has vanishing monomial moments of parabolic degree `< N`. We record them in
the structure `ShellProfile`, and show that both `annKernel0 N` and the causal profile
`annKernel0C N` satisfy it. The profile-generic copies of the abstract developments live in
`RegularityStructures.Abstract.Profile`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 5.5.
-/
@[expose] public section
namespace RegularityStructures
open scoped ContDiff in
/-- A kernel profile for the shells `K_n = scaledShell h n`: smooth, supported in the closed unit
parabolic ball, with vanishing moments up to parabolic degree `< N` (cf. [Hai14, Lemma 5.5]). -/
structure ShellProfile (h : ParabolicSpace → ℝ) (N : ℕ) : Prop where
  contDiff : ContDiff ℝ ∞ h
  eq_zero : ∀ z, 1 < parabolicNorm z → h z = 0
  moment : ∀ k : PolyIndex N, ∫ z, monoFn k.1 z * h z = 0
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Heat.Schauder.TaylorSum ====
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
# The iterated Taylor polynomial as a sum over a box of multi-indices

`tyOp s m J φ (w) = ∑_{k ∈ boxSet m J} coeffT s k · D^k φ (w)` for `J` without repetitions, where
`boxSet m J = {k : supp k ⊆ J, k_i ≤ m_i}` and `coeffT s k = ∏_i s_i^{k_i}/k_i!`
(`tyOp_eq_sum`).  Here `D^k = lineIter (multiDirs k)`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The Taylor coefficient `∏ᵢ sᵢ^{kᵢ} / kᵢ!` of the multi-index `k`. -/
def coeffT (s : Fin 4 → ℝ) (k : Fin 4 →₀ ℕ) : ℝ :=
  ∏ i, s i ^ k i / ((Nat.factorial (k i) : ℕ) : ℝ)
/-- The box of multi-indices supported on `J` with `kᵢ ≤ mᵢ`, built recursively. -/
def boxSet (m : Fin 4 → ℕ) : List (Fin 4) → Finset (Fin 4 →₀ ℕ)
  | [] => {0}
  | j :: J => ((boxSet m J) ×ˢ (Finset.range (m j + 1))).image
      (fun q => q.1 + Finsupp.single j q.2)
end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Heat.Schauder.TaylorKernel ====
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
# The Taylor-remainder kernel `K^α_{n;xy}`

`taylorIdx σ = {k : |k|_𝔰 < σ}` (a finite set) and

  `taylorKernel h n σ x y (w) = g(y - w) - ∑_{k ∈ taylorIdx σ} (y - x)^k/k! · D^k g(x - w)`,
  `g = scaledShell h n`,

is Hairer's `K^α_{n;xy}` [Hai14, (5.14)] with `σ = α + β`.  We show it is the profile
`H(u) = g(u + (y - x)) - ∑ c_k D^k g(u)` evaluated at `x - w`, and that
`H = (remJ …)(−u) + ∑_{k ∈ box, |k|_𝔰 ≥ σ} c_k D^k g` (`taylorProfile_eq`), where `remJ` is the
box Taylor remainder of `TaylorBox.lean`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The multi-indices `k` with `|k|_𝔰 < σ`, as a finite set. -/
def taylorIdx (σ : ℝ) : Finset (Fin 4 →₀ ℕ) :=
  (boxSet (fun _ => ⌈σ⌉₊) (List.finRange 4)).filter fun k => (multiDeg k : ℝ) < σ

/-- `k! = ∏ᵢ kᵢ!`. -/
def multiFact (k : Fin 4 →₀ ℕ) : ℝ := ∏ i, ((Nat.factorial (k i) : ℕ) : ℝ)
/-- `K^α_{n;xy}(w) = K_n(y - w) - ∑_{|k|_𝔰 < σ} (y - x)^k/k! D^k K_n(x - w)`, `K_n = scaledShell h n`. -/
def taylorKernel (h : ParabolicSpace → ℝ) (n : ℕ) (σ : ℝ) (x y : ParabolicSpace)
    (w : ParabolicSpace) : ℝ :=
  scaledShell h n (y - w) - ∑ k ∈ taylorIdx σ,
    (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
      lineIter (multiDirs k) (scaledShell h n) (x - w)

end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Profile.RealGerm ====
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
# The germ of a realised integral, for a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.Realising.Germ` and of the
measurability part of `RegularityStructures.Abstract.Integration.Realising.Measurable`. For a model
`M`, a basis index `i` and a kernel profile `h` (`ShellProfile h N`), the germ is
`realGermP M h x i y = ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` with `K_n = scaledShell h n` [Hai14, Remark
5.10]. It converges absolutely with
`|realGermP M h x i y| ≤ c C_Π max(C_Γ, 1) ‖y - x‖_𝔰^{deg i + 2}` (`exists_abs_realGerm_leP`) and is
measurable (`measurable_realGermP`).

Source: [Hai14] = arXiv:1303.5113v4, Definition 5.9, Remark 5.10, (5.14), Lemma 5.19.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
/-- `y ↦ ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` with `K_n = scaledShell h n`: the density of
`Π_x I e_i` against Lebesgue measure in Hairer's Remark 5.10. -/
def realGermP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (i : ι) (y : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing (fun t z => M.regPi x (Pi.single i 1) t z)
    (taylorKernel h n (𝒯.deg i + 2) x y)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Polynomial.Model.Reg ====
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
# Polynomials as `Q`-distributions

The polynomial `z ↦ (z - x)^τ = polyEval x τ z` has polynomial growth, so it is integrable against
`q_t(y - ·)` and `Q_s Q_t (polyEval x τ) = Q_{s+t} (polyEval x τ)`. Its family of regularisations
`polyReg x τ t = Q_t (polyEval x τ)` (and `0` for `t ≤ 0`) is a `Q`-distribution
(`polyReg_mem`), linear in `τ`. This records `Π_x τ` for the polynomial model
[Hai14, Section 2.2, Remark 2.23, (2.20)].
-/
@[expose] public section
open MeasureTheory
namespace RegularityStructures
variable {N : ℕ}
/-- The regularisations `t ↦ Q_t (z ↦ (z - x)^τ)` of the polynomial `(· - x)^τ`, extended by `0` to
`t ≤ 0`. -/
noncomputable def polyReg (x : ParabolicSpace) (τ : PolyIndex N → ℝ) :
    ℝ → ParabolicSpace → ℝ := fun t y =>
  if 0 < t then parabolicSemigroup.apply t (polyEval x τ) y else 0
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
variable {N : ℕ}

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Integration.Realising.Def ====
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
# Models realising a kernel for an abstract integration map

[Hai14, Definition 5.9, Remark 5.10]: a model `(Π, Γ)` realises `K` for `I` if
`Π_x I a = ∫ K(·, z) (Π_x a)(dz) - Π_x J(x) a`; rigorously
`(Π_x I a)(ψ) = ∑_n ∫ ψ(y) (Π_x a)(K^α_{n;xy}) dy`. With distributions recorded as `Q`-families,
for the basis vectors `e_i` of the sector `V` of degree `deg i < γ` this reads

  `(Q_t Π_x I e_i)(z) = realReg M N x i t z = ∫ Q_t(z, y) g_{x,i}(y) dy`,

with `K_n = annShell N n` (`RealisesKernel`). The polynomial part of Definition 5.9 (and
Assumption 5.3) is a separate predicate `IsPolyCompatible`: `Π_x X^k = (· - x)^k`, recorded as the
`Q`-family `polyReg`. `IsRealising` is their conjunction.
-/
@[expose] public section
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
namespace Model
/-- `Π_x X^k = (· - x)^k` for the abstract polynomials of `P` [Hai14, Assumption 5.3]: the
regularisations of `Π_x e_{P.emb k}` are those of the polynomial `(· - x)^k`. -/
def IsPolyCompatible (M : Model 𝒯 parabolicSemigroup) {N' : ℕ} (P : PolynomialSector 𝒯 N') :
    Prop :=
  ∀ (x : ParabolicSpace) (k : PolyIndex N') (t : ℝ) (z : ParabolicSpace),
    M.regPi x (Pi.single (P.emb k) 1) t z = polyReg x (Pi.single k 1) t z
end Model
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Profile.Realising ====
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
# Models realising a kernel with a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.Realising.Reg` and
`RegularityStructures.Abstract.Integration.Realising.Def`, with the consistency bound. A model
`(Π, Γ)` realises `K = ∑_n scaledShell h n` for `I` [Hai14, Definition 5.9, Remark 5.10] if, for the
basis vectors `e_i` of the sector `V` with `deg i < γ`,
`Q_t Π_x I e_i = realRegP M h x i t = Q_t g_{x,i}` for `t > 0` (`Model.RealisesKernelP`); the
polynomial part `IsPolyCompatible` does not involve the kernel and is reused. `Model.IsRealisingP`
is their conjunction. The germ `g_{x,i} = realGermP M h x i` has polynomial growth
(`polyBounded_realGermP`), and the consistency bound at degree `deg i + 2` holds
(`abs_regPi_integral_leP`).

Source: [Hai14] = arXiv:1303.5113v4, Definition 5.9, Remark 5.10.
-/
@[expose] public noncomputable section
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
/-- The `Q`-family `t ↦ Q_t g_{x,i}` of the realised distribution
`ψ ↦ ∫ ψ(y) ∑_n (Π_x e_i)(K^{deg i}_{n;xy}) dy`, extended by `0` to `t ≤ 0`. -/
def realRegP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (i : ι) : ℝ → ParabolicSpace → ℝ := fun t z =>
  if 0 < t then parabolicSemigroup.apply t (realGermP M h x i) z else 0
namespace Model
/-- The clause of [Hai14, Definition 5.9] on the basis vectors `e_i`, `deg i < γ`, of `V`:
`Q_t Π_x I e_i = Q_t g_{x,i}` for `t > 0` (kernel `K_n = scaledShell h n`). -/
def RealisesKernelP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (γ : ℝ)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ (x : ParabolicSpace) (i : ι), 𝒯.deg i < γ → (Pi.single i 1 : ι → ℝ) ∈ V →
    ∀ t : ℝ, 0 < t → ∀ z : ParabolicSpace,
      M.regPi x (I (Pi.single i 1)) t z = realRegP M h x i t z
/-- `M` realises the kernel with profile `h` for `I` [Hai14, Definition 5.9]: the integral clause
(`RealisesKernelP`) and compatibility with the polynomials of `P` (`IsPolyCompatible`). -/
structure IsRealisingP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (γ : ℝ)
    {N' : ℕ} (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (V : Submodule ℝ (ι → ℝ)) : Prop where
  realises : M.RealisesKernelP h γ I V
  poly : M.IsPolyCompatible P
end Model
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {h : ParabolicSpace → ℝ} {N : ℕ}

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Ext514W.SettingNear ====
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
# The standing hypotheses of the extension estimates, near-pair `Γ`-bounds

`ExtSettingWNear` assumes the bounds `PiBoundOn γ CPi` and `GammaNearOn γ CGam` only on Hairer's
window `hairerTimeWindow = [-1, 2] × ℝ³`, together with a qualitative growth model (used only for
the existence and linearity of the pairings and for identities, never in a constant) and the degree
condition `-4 < deg j` for all `deg j < γ`.

The structural lemmas about `τ = Γ_{yx} e_i` for base points in the window: `τ ∈ V ∩ T_{<γ}`
(`ExtSettingWNear.gammaMap_single_mem`), its support (`ExtSettingWNear.gammaMap_single_support`) and
`|τ_j| ≤ max(C_Γ, 1) d^{deg i − deg j}` (`ExtSettingWNear.abs_gammaMap_single_le`).

The `Γ`-bound `GammaNearOn` (`RegularityStructures.Abstract.ModelNear`) holds only for near pairs
and replaces `GammaBoundOn`.
-/
public section
open Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
namespace Model
/-- The standing hypotheses of the extension theorem estimates, window version: the model bounds
hold on `hairerTimeWindow`, with a qualitative growth model. -/
structure ExtSettingWNear (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (N : ℕ) (γ : ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (CPi CGam : ℝ) : Prop where
  profile : ShellProfile h N
  realising : M.IsRealisingP h γ P I V
  integration : IsAbstractIntegration P V I 2
  sector : 𝒯.IsSector V
  basis_mem : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V
  deg_gtV : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j
  deg_gt4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j
  piBound : M.PiBoundOn γ CPi hairerTimeWindow
  gammaBound : M.GammaNearOn γ CGam hairerTimeWindow
  piBound_nonneg : 0 ≤ CPi
  growth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
    M.GrowthModel γ C' C'' ρP ρG p q
  poly_largeV : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ →
    ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N'
  integration_poly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0
  poly_le : N' ≤ N
variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ} {γ CPi CGam : ℝ}
  {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

end Model
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Heat.Schauder.Derivative ====
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
# Pairing with derivatives of the dyadic pieces

For `h` smooth and supported in the unit parabolic ball, a multi-index `k`, and `Λ` of local order
`α` at `x` with exponent set `A`:
`|⟨Λ, D^k (scaledShell h n)(x - ·)⟩| ≤ c C 2^{(|k|_𝔰 - α - 2) n}` (`abs_pairing_lineIter_scaledShell_le`),
with `c = derivShellConst h k A` independent of `Λ, C, x, n`.  If `|k|_𝔰 < α + 2` the series over `n`
converges absolutely (`summable_pairing_lineIter_scaledShell`) and its sum is bounded by
`c C / (1 - 2^{|k|_𝔰 - α - 2})` (`abs_tsum_pairing_lineIter_scaledShell_le`).  This is the estimate
behind Hairer's map `J(x)` [Hai14, (5.11)].
-/
@[expose] public noncomputable section
namespace RegularityStructures

/-- The `n`-th term: `⟨Λ, D^k (scaledShell h n)(x - ·)⟩`. -/
def derivShellPairing (Λ : ℝ → ParabolicSpace → ℝ) (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ)
    (x : ParabolicSpace) (n : ℕ) : ℝ :=
  parabolicSemigroup.pairing Λ (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))

end RegularityStructures
end
public section
open MeasureTheory Set
open scoped ContDiff
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Abstract.Ext514.Bracket ====
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
# The series for the polynomial components of `Γ_{yx} I e_i`

`extU M h x y i k n = ∑_{j : |k| < deg j + 2} τ_j ⟨Π_y e_j, D^k K_n(y − ·)⟩ −
 ∑_{|l| < σ} (y−x)^l/l! ⟨Π_x e_i, D^{k+l} K_n(x − ·)⟩`, `τ = Γ_{yx} e_i`, `σ = deg i + 2 − |k|`
(the `n`-th term of [Hai14, (5.38)], with the roles of `x, y` exchanged).
`Model.poly_bracket_ext`: `k! (Γ_{yx} I e_i)_{X^k} = ∑_n extU n` and the series is summable.
-/
@[expose] public noncomputable section
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
open scoped Classical in
/-- The `n`-th term of the series for the `X^k` component of `Γ_{yx} I e_i`. -/
def extU (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x y : ParabolicSpace) (i : ι)
    (k : Fin 4 →₀ ℕ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j => (multiDeg k : ℝ) < 𝒯.deg j + 2),
    M.gammaMap y x (Pi.single i 1) j *
      derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n) -
  ∑ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
    derivShellPairing (fun t z => M.regPi x (Pi.single i 1) t z) h (k + l) x n
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_8c984b58b001910de311_PolyBoundNear ====
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
# Bound on the polynomial series of `Γ_{yx} I e_i`, near-pair `Γ`-bounds

Under `ExtSettingWNear`, for `x, y ∈ timeSlab 1` with `0 < d(y, x) ≤ gammaNearRadius`, the series
`∑ₙ extU n` converges and is bounded by `c C_Π max(C_Γ, 1)² d(y, x)^{deg i + 2 − |k|}`, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/
public section
open Set
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ}
namespace Model
set_option linter.unusedVariables false in
theorem exists_abs_tsum_extU_le_win_near (hh : ShellProfile h N) {γ : ℝ} (V : Submodule ℝ (ι → ℝ))
    (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (P : PolynomialSector 𝒯 N') {i : ι} (hi : 𝒯.deg i < γ)
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (k : Fin 4 →₀ ℕ)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2)
    (hnat1 : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ 𝒯.deg i + 2 - multiDeg k)
    (hnat2 : ∀ j, j ∉ Set.range P.emb → (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j ≤ 𝒯.deg i →
      (multiDeg k : ℝ) ≠ 𝒯.deg j + 2) 
    (h_RegularityStructures_Model_exists_abs_extU_le_of_one_lt_win_near : ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι]
      {𝒯 : RegularityStructures.RegularityStructure ι} {N' : ℕ}
      {h : RegularityStructures.ParabolicSpace → ℝ} {N : ℕ},
      RegularityStructures.ShellProfile h N →
        ∀ {γ : ℝ} (V : Submodule ℝ (ι → ℝ)),
          (∀ (j : ι), 𝒯.deg j < γ → -4 < 𝒯.deg j) →
            ∀ (P : RegularityStructures.PolynomialSector 𝒯 N') {i : ι},
              𝒯.deg i < γ →
                Pi.single i 1 ∈ V →
                  ∀ (k : Fin 4 →₀ ℕ),
                    ∃ (b : ℝ) (C : ℝ),
                      0 < b ∧
                        0 ≤ C ∧
                          ∀ (M : RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup)
                            {CPi CGam : ℝ} (I : (ι → ℝ) →ₗ[ℝ] ι → ℝ),
                            M.ExtSettingWNear h N γ P I V CPi CGam →
                              ∀ {x y : RegularityStructures.ParabolicSpace},
                                x ∈ RegularityStructures.timeSlab 1 →
                                  y ∈ RegularityStructures.timeSlab 1 →
                                    0 < RegularityStructures.parabolicNorm (y - x) →
                                      RegularityStructures.parabolicNorm (y - x) ≤
                                          RegularityStructures.gammaNearRadius →
                                        ∀ (n : ℕ),
                                          1 < 2 ^ n * RegularityStructures.parabolicNorm (y - x) →
                                            |RegularityStructures.extU M h x y i k n| ≤
                                              C *
                                                  (CPi * Max.max CGam 1 * Max.max CGam 1 *
                                                    RegularityStructures.parabolicNorm (y - x) ^
                                                      (𝒯.deg i + 2 -
                                                        (↑(RegularityStructures.multiDeg k) : ℝ))) *
                                                (2 ^ n * RegularityStructures.parabolicNorm (y - x)) ^
                                                  (-b))
    (h_RegularityStructures_KGammaSup_exists_summable_abs_tsum_le : ∀ (a b : ℝ),
      0 < a →
        0 < b →
          ∃ (C : ℝ),
            0 ≤ C ∧
              ∀ (w : ℝ),
                0 < w →
                  ∀ (u : ℕ → ℝ) (B : ℝ),
                    0 ≤ B →
                      (∀ (n : ℕ), |u n| ≤ B * Min.min ((2 ^ n * w) ^ a) ((2 ^ n * w) ^ (-b))) →
                        Summable u ∧ ∑' (n : ℕ), |u n| ≤ C * B)
    (h_RegularityStructures_Model_exists_abs_extU_le_of_le_one_win_near : ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι]
      {𝒯 : RegularityStructures.RegularityStructure ι} {N' : ℕ}
      {h : RegularityStructures.ParabolicSpace → ℝ} {N : ℕ},
      RegularityStructures.ShellProfile h N →
        ∀ {γ : ℝ} (V : Submodule ℝ (ι → ℝ)),
          (∀ (j : ι), 𝒯.deg j < γ → -4 < 𝒯.deg j) →
            ∀ (P : RegularityStructures.PolynomialSector 𝒯 N') {i : ι},
              𝒯.deg i < γ →
                Pi.single i 1 ∈ V →
                  ∀ (k : Fin 4 →₀ ℕ),
                    (↑(RegularityStructures.multiDeg k) : ℝ) < 𝒯.deg i + 2 →
                      (∀ (l : Fin 4 →₀ ℕ),
                          (↑(RegularityStructures.multiDeg l) : ℝ) ≠
                            𝒯.deg i + 2 - (↑(RegularityStructures.multiDeg k) : ℝ)) →
                        (∀ j ∉ Set.range P.emb,
                            Pi.single j 1 ∈ V →
                              𝒯.deg j ≤ 𝒯.deg i →
                                (↑(RegularityStructures.multiDeg k) : ℝ) ≠ 𝒯.deg j + 2) →
                          ∃ (a : ℝ) (C : ℝ),
                            0 < a ∧
                              0 ≤ C ∧
                                ∀
                                  (M :
                                    RegularityStructures.Model 𝒯
                                      RegularityStructures.parabolicSemigroup)
                                  {CPi CGam : ℝ} (I : (ι → ℝ) →ₗ[ℝ] ι → ℝ),
                                  M.ExtSettingWNear h N γ P I V CPi CGam →
                                    ∀ {x y : RegularityStructures.ParabolicSpace},
                                      x ∈ RegularityStructures.timeSlab 1 →
                                        y ∈ RegularityStructures.timeSlab 1 →
                                          0 < RegularityStructures.parabolicNorm (y - x) →
                                            ∀ (n : ℕ),
                                              2 ^ n * RegularityStructures.parabolicNorm (y - x) ≤ 1 →
                                                |RegularityStructures.extU M h x y i k n| ≤
                                                  C *
                                                      (CPi * Max.max CGam 1 * Max.max CGam 1 *
                                                        RegularityStructures.parabolicNorm (y - x) ^
                                                          (𝒯.deg i + 2 -
                                                            (↑(RegularityStructures.multiDeg k) : ℝ))) *
                                                    (2 ^ n *
                                                        RegularityStructures.parabolicNorm (y - x)) ^
                                                      a)
    :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)), M.ExtSettingWNear h N γ P I V CPi CGam →
      ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 → 0 < parabolicNorm (y - x) →
      parabolicNorm (y - x) ≤ gammaNearRadius →
      Summable (extU M h x y i k) ∧
      |∑' n, extU M h x y i k n| ≤
        c * CPi * max CGam 1 * max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i + 2 - multiDeg k) := by
  obtain ⟨b, Cs, hb, hCs0, Hs⟩ := h_RegularityStructures_Model_exists_abs_extU_le_of_one_lt_win_near hh V hdeg4 P hi hVi k
  obtain ⟨a, Cl, ha, hCl0, Hl⟩ := h_RegularityStructures_Model_exists_abs_extU_le_of_le_one_win_near hh V hdeg4 P hi hVi k hk hnat1
    hnat2
  obtain ⟨Cg, hCg0, hCg⟩ := h_RegularityStructures_KGammaSup_exists_summable_abs_tsum_le a b ha hb
  refine ⟨Cg * max Cs Cl, mul_nonneg hCg0 (hCs0.trans (le_max_left _ _)),
    fun M CPi CGam I S x y hx hy hd hxy => ?_⟩
  have hCw1 : 1 ≤ max CGam 1 := le_max_right _ _
  have hCw0 : 0 ≤ max CGam 1 := zero_le_one.trans hCw1
  have hCPi := S.piBound_nonneg
  set d := parabolicNorm (y - x) with hddef
  set σ : ℝ := 𝒯.deg i + 2 - multiDeg k with hσdef
  have hdσ : 0 ≤ d ^ σ := Real.rpow_nonneg hd.le σ
  set Y : ℝ := CPi * max CGam 1 * max CGam 1 * d ^ σ with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hmax0 : 0 ≤ max Cs Cl := hCs0.trans (le_max_left _ _)
  have hbound : ∀ n : ℕ, |extU M h x y i k n| ≤
      (max Cs Cl * Y) * min (((2 : ℝ) ^ n * d) ^ a) (((2 : ℝ) ^ n * d) ^ (-b)) := by
    intro n
    have hu : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    set s : ℝ := (2 : ℝ) ^ n * d with hsdef
    have hs0 : 0 < s := by rw [hsdef]; positivity
    rcases le_or_gt s 1 with hs1 | hs1
    · have := Hl M I S hx hy hd n hs1
      have hmin : min (s ^ a) (s ^ (-b)) = s ^ a := by
        refine min_eq_left ?_
        calc s ^ a ≤ 1 := Real.rpow_le_one hs0.le hs1 ha.le
          _ ≤ s ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 (by linarith)
      rw [hmin]
      refine this.trans ?_
      have h2 : 0 ≤ Y * s ^ a := mul_nonneg hY0 (Real.rpow_nonneg hs0.le _)
      calc Cl * Y * s ^ a = Cl * (Y * s ^ a) := by ring
        _ ≤ max Cs Cl * (Y * s ^ a) := mul_le_mul_of_nonneg_right (le_max_right _ _) h2
        _ = _ := by ring
    · have := Hs M I S hx hy hd hxy n hs1
      have hmin : min (s ^ a) (s ^ (-b)) = s ^ (-b) := by
        refine min_eq_right ?_
        calc s ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1.le (by linarith)
          _ ≤ s ^ a := Real.one_le_rpow hs1.le ha.le
      rw [hmin]
      refine this.trans ?_
      have h2 : 0 ≤ Y * s ^ (-b) := mul_nonneg hY0 (Real.rpow_nonneg hs0.le _)
      calc Cs * Y * s ^ (-b) = Cs * (Y * s ^ (-b)) := by ring
        _ ≤ max Cs Cl * (Y * s ^ (-b)) := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
        _ = _ := by ring
  obtain ⟨hs, hb'⟩ := hCg d hd (extU M h x y i k) (max Cs Cl * Y) (mul_nonneg hmax0 hY0) hbound
  refine ⟨hs, ?_⟩
  have h1 : |∑' n, extU M h x y i k n| ≤ ∑' n, |extU M h x y i k n| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  refine h1.trans (hb'.trans (le_of_eq ?_))
  rw [hY]; ring
end Model
end RegularityStructures
end
