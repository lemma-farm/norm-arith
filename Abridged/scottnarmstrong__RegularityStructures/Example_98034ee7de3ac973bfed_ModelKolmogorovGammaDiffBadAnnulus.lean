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
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.MeanInequalitiesPow

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Abstract.RegularityStructure ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Semigroup.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Abstract.Model ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Kernel.Symbol ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Kernel.Quartic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Kernel.Gaussian ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Parabolic.Basic ====
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

end RegularityStructures
end
public section
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.parabolicNorm_nonneg : ∀ (z : RegularityStructures.ParabolicSpace), 0 ≤ RegularityStructures.parabolicNorm z

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Kernel.Parabolic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Kernel.Moments ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Kernel.ParabolicSemigroup ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovHSParabolicGrid ====
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
# Parabolic dyadic grids for the model Kolmogorov criterion

The covering argument of Hairer--Steele, arXiv:2301.10081v3, Proposition B.3,
uses the scaling dimension rather than the topological dimension. On the unit
space-time box the time mesh is `2^(-2n)` and the three spatial meshes are
`2^(-n)`. Thus the grid has at most `16 * 2^(5n)` points.

These grids are deterministic geometry, independent of any random-model or
pathwise-bound hypothesis.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- Indices of the anisotropic dyadic grid in the unit space-time box. -/
abbrev HSParabolicGridIndex (n : ℕ) :=
  Fin (2 ^ (2 * n) + 1) × (Fin 3 → Fin (2 ^ n + 1))

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovHSCompactNet ====
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
# Finite nets whose representatives remain inside the compact

Hairer--Steele, arXiv:2301.10081v3, Proposition B.3 assumes moment bounds
only at points of the compact. Replacing the compact by a containing box in
the stochastic hypotheses would strengthen the statement. Instead we retain
one representative of each occupied anisotropic grid cell. This construction
works for any subset of the unit box, including the empty set, and has the
same dimension-five cardinality bound as the ambient grid.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- Clipped dyadic cell index; clipping makes it defined on every real number. -/
def hsDyadicCellIndex (n : ℕ) (x : ℝ) : Fin (2 ^ n + 1) :=
  ⟨min (Nat.floor (x * (2 : ℝ) ^ n)) (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩
/-- The time-space cell index with the parabolic time refinement. -/
def hsParabolicCellIndex (n : ℕ) (x : ParabolicSpace) : HSParabolicGridIndex n :=
  (hsDyadicCellIndex (2 * n) x.1, fun j => hsDyadicCellIndex n (x.2 j))
/-- Occupied cells carry witnesses in the original set, not in a larger neighbourhood. -/
abbrev HSParabolicOccupiedCell (S : Set ParabolicSpace) (n : ℕ) :=
  {i : HSParabolicGridIndex n // ∃ x : S, hsParabolicCellIndex n x = i}

/-- A selected point of the original set in each occupied cell. -/
def hsParabolicCellRepresentative (S : Set ParabolicSpace) (n : ℕ)
    (i : HSParabolicOccupiedCell S n) : S := Classical.choose i.property

end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovHSCompactParent ====
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
# Parent cells for intrinsic parabolic nets

The occupied-cell nets used in Hairer--Steele, arXiv:2301.10081v3,
Proposition B.3 must be compatible across scales. Dyadic floor division
shows that a fine cell lies in one coarse cell. Hence each occupied fine
cell has an occupied parent, and the two selected representatives are
within the coarse parabolic mesh radius. No enlargement of the stochastic
index set is involved.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The coarse occupied cell of a chosen fine representative. -/
def hsParabolicCellParent (S : Set ParabolicSpace) (n : ℕ)
    (i : HSParabolicOccupiedCell S (n + 1)) : HSParabolicOccupiedCell S n :=
  ⟨hsParabolicCellIndex n (hsParabolicCellRepresentative S (n + 1) i),
    hsParabolicCellRepresentative S (n + 1) i, rfl⟩
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.KolmogorovChentsovScale ====
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
# Dyadic scale selection on the unit interval

The radius `4 * 2⁻ⁿ` is the scale appearing in the finite close-pair
estimates.  This file proves that it is comparable to every nonzero distance
on the unit interval, with constants independent of the points.
-/
@[expose] public section
open scoped ENNReal NNReal Topology
namespace RegularityStructures
noncomputable def dyadicBase (n : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ n

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovGammaProductNet ====
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
# Product-net increments for Gamma chaining

At a fixed parabolic scale the two base points are selected independently from
the occupied cells of the compact.  The definitions below retain that product
net explicitly.  Their moment lemmas are the finite, source-facing part of the
annular argument: no model norm or random bound is used as a premise.
-/
@[expose] public noncomputable section
open MeasureTheory
open Filter
open scoped ENNReal NNReal Topology
namespace RegularityStructures
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
abbrev gammaCell (S : Set ParabolicSpace) (n : ℕ) :=
  HSParabolicOccupiedCell S n

/-!
The next three lemmas use the source estimates at exactly the representative
pairs selected by the net.  The endpoint estimates are kept separate because
the later telescoping proof must preserve both Chen channels.
-/

/-!
The parent-child decomposition is the deterministic telescope used to pass from
the finite product nets to a genuine two-base-point field.  The orientation of
the right-step definition is chosen so that the intermediate value has the
fine first endpoint and the fine second endpoint.
-/

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovGammaSplit ====
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
# The `DΓ` / non-`DΓ` split in the Gamma Chen source

For a strictly lower Gamma coordinate, the Chen source is a finite sum of products. The products
whose two factors are in the deterministic sector `DΓ` are separated from the remaining products.
The former are controlled pathwise and the latter retain the moment reserve. This is the
source-level split used in the finite-sector induction of the Kolmogorov criterion for models.

The identities are the coordinate form of Hairer [Hai14, (2.17)] and the mixed endpoint formula used
in [Hai14, Theorem 10.7].
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}
/-- The indices strictly intermediate between `j` and `i`. -/
def gammaIntermediate (𝒯 : RegularityStructure ι) (i j : ι) : Finset ι :=
  by
    classical
    exact Finset.univ.filter
      (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i)
/-- The intermediate indices with at least one non-deterministic factor. -/
def gammaGoodIntermediate (𝒯 : RegularityStructure ι)
    (D : Set (ι × ι)) (i j : ι) : Finset ι :=
  by
    classical
    exact (gammaIntermediate 𝒯 i j).filter
      (fun k => ¬((i, k) ∈ D ∧ (k, j) ∈ D))
/-- The intermediate indices with two deterministic factors. -/
def gammaBadIntermediate (𝒯 : RegularityStructure ι)
    (D : Set (ι × ι)) (i j : ι) : Finset ι :=
  by
    classical
    exact (gammaIntermediate 𝒯 i j).filter
      (fun k => (i, k) ∈ D ∧ (k, j) ∈ D)

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovGammaDiffSplit ====
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
# Pathwise two-deterministic-factor Gamma channels

The finite-sector Gamma induction separates the Chen products whose two
coordinates are in `DΓ`.  This file records the corresponding pathwise
estimates, including the two-model difference formula.  These channels spend
no `κbar` reserve; their endpoint refinement is summed geometrically using
the positive degree of the fine factor.

The algebra is the coordinate form of Hairer [Hai14, (2.17)] and the
two-model expansion used in [Hai14, Theorem 10.7], arXiv:1303.5113v4.
-/
@[expose] public noncomputable section
open Set
open scoped ENNReal
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}
def gammaSplitLeftBadTermDiff
    (M₁ M₂ : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) : ℝ :=
  ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
    ((M₁.gammaMap y x (Pi.single i 1) k -
        M₂.gammaMap y x (Pi.single i 1) k) *
      M₁.gammaMap z y (Pi.single k 1) j +
      M₂.gammaMap y x (Pi.single i 1) k *
        (M₁.gammaMap z y (Pi.single k 1) j -
          M₂.gammaMap z y (Pi.single k 1) j))

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovGammaDiffSource ====
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
# Good-channel source moments for two-model Gamma differences

The two-model Chen source is split before applying Holder.  This file keeps
the channels having at least one non-`DΓ` factor.  Such a channel retains the
`κbar` reserve supplied by the non-deterministic factor; the complementary
two-`DΓ` channel is handled pathwise.
-/
@[expose] public noncomputable section
open MeasureTheory Set Classical
open scoped ENNReal NNReal
namespace RegularityStructures
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}
def gammaDiffSplitLeftGoodTerm
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) (ω : Ω) : ℝ :=
  (M₁ ω).gammaMap z y (Pi.single i 1) j -
      (M₂ ω).gammaMap z y (Pi.single i 1) j +
    ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
      (((M₁ ω).gammaMap y x (Pi.single i 1) k -
          (M₂ ω).gammaMap y x (Pi.single i 1) k) *
          (M₁ ω).gammaMap z y (Pi.single k 1) j +
        (M₂ ω).gammaMap y x (Pi.single i 1) k *
          ((M₁ ω).gammaMap z y (Pi.single k 1) j -
            (M₂ ω).gammaMap z y (Pi.single k 1) j))

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovGammaDiffRelativeSource ====
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
# Split annular sources for the two-model Gamma difference

The annular increment is split before any supremum or moment estimate. The good term is the
complement of `DΓ × DΓ`; the bad term is the finite pathwise sector. This is the algebra on the side
of the source bounds in the Kolmogorov criterion for models.
-/
@[expose] public noncomputable section
open MeasureTheory Set Classical
open scoped ENNReal NNReal
namespace RegularityStructures
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}
def gammaDiffGoodLeftAnnulusStepSup
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a)) ω‖ₑ
    else 0
def gammaDiffBadLeftAnnulusStepSup
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaSplitLeftBadTermDiff (M₁ ω) (M₂ ω) D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))‖ₑ
    else 0

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_98034ee7de3ac973bfed_ModelKolmogorovGammaDiffBadAnnulus ====
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
# Pathwise annular bounds for the difference `DΓ × DΓ` channel

The difference of two Chen products is a sum of two terms.  When both
coordinates belong to `DΓ`, one factor is controlled pathwise by the
deterministic model estimate and the other by the pathwise difference
estimate.  The positive degree of the fine factor gives the geometric
endpoint reserve.  This is the difference analogue of the pathwise part of
Hairer [Hai14, (2.17)].
-/
@[expose] public noncomputable section
open Set
open scoped ENNReal
namespace RegularityStructures
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}


set_option linter.unusedVariables false in
theorem gammaDiffBadLeftStepSupAnnulus_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C d r : ℝ) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdet₁ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₁ ω).gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdet₂ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₂ ω).gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdiff : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₁ ω).gammaMap v u (Pi.single a 1) b -
        (M₂ ω).gammaMap v u (Pi.single a 1) b| ≤
        d * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (i j : ι) (hi : 𝒯.deg i < γ) (hij : 𝒯.deg j < 𝒯.deg i)
    (β : ℝ) (hβ : β = 𝒯.deg i - 𝒯.deg j) (_hr : 0 < r)
    (hgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      r ≤ 𝒯.deg k - 𝒯.deg j)
    (ω : Ω) (N l : ℕ) 
    (h_RegularityStructures_gammaDiffBad_left_geometry : ∀ (S : Set RegularityStructures.ParabolicSpace),
      (∀ x ∈ S, x.1 ∈ Set.Icc 0 1 ∧ ∀ (j : Fin 3), x.2 j ∈ Set.Icc 0 1) →
        ∀ (N k : ℕ),
          N ≤ k →
            ∀ (a b : RegularityStructures.gammaCell S (k + 1)),
              RegularityStructures.parabolicNorm
                    ((↑(RegularityStructures.hsParabolicCellRepresentative S k
                            (RegularityStructures.hsParabolicCellParent S k a)) :
                        RegularityStructures.ParabolicSpace) -
                      (↑(RegularityStructures.hsParabolicCellRepresentative S (k + 1) b) :
                        RegularityStructures.ParabolicSpace)) ≤
                  20 / 2 ^ N →
                RegularityStructures.parabolicNorm
                      ((↑(RegularityStructures.hsParabolicCellRepresentative S (k + 1) a) :
                          RegularityStructures.ParabolicSpace) -
                        (↑(RegularityStructures.hsParabolicCellRepresentative S (k + 1) b) :
                          RegularityStructures.ParabolicSpace)) ≤
                    24 / 2 ^ N ∧
                  RegularityStructures.parabolicNorm
                      ((↑(RegularityStructures.hsParabolicCellRepresentative S k
                              (RegularityStructures.hsParabolicCellParent S k a)) :
                          RegularityStructures.ParabolicSpace) -
                        (↑(RegularityStructures.hsParabolicCellRepresentative S (k + 1) a) :
                          RegularityStructures.ParabolicSpace)) ≤
                    4 / 2 ^ k)
    (h_RegularityStructures_gammaSplitLeftBadTermDiff_enorm_le : ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι]
      {𝒯 : RegularityStructures.RegularityStructure ι}
      (M₁ M₂ : RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup) (D : Set (ι × ι))
      (γ C δ : ℝ),
      0 ≤ C →
        0 ≤ δ →
          ∀ (i j : ι) (x y z : RegularityStructures.ParabolicSpace),
            𝒯.deg i < γ →
              𝒯.deg j < 𝒯.deg i →
                (∀ (a b : ι),
                    (a, b) ∈ D →
                      𝒯.deg a < γ →
                        𝒯.deg b < 𝒯.deg a →
                          ∀ (u v : RegularityStructures.ParabolicSpace),
                            |(M₁.gammaMap v u : (ι → ℝ) → ι → ℝ) (Pi.single a 1) b| ≤
                              C *
                                RegularityStructures.parabolicSemigroup.scaleDist v u ^
                                  (𝒯.deg a - 𝒯.deg b)) →
                  (∀ (a b : ι),
                      (a, b) ∈ D →
                        𝒯.deg a < γ →
                          𝒯.deg b < 𝒯.deg a →
                            ∀ (u v : RegularityStructures.ParabolicSpace),
                              |(M₂.gammaMap v u : (ι → ℝ) → ι → ℝ) (Pi.single a 1) b| ≤
                                C *
                                  RegularityStructures.parabolicSemigroup.scaleDist v u ^
                                    (𝒯.deg a - 𝒯.deg b)) →
                    (∀ (a b : ι),
                        (a, b) ∈ D →
                          𝒯.deg a < γ →
                            𝒯.deg b < 𝒯.deg a →
                              ∀ (u v : RegularityStructures.ParabolicSpace),
                                |(M₁.gammaMap v u : (ι → ℝ) → ι → ℝ) (Pi.single a 1) b -
                                      (M₂.gammaMap v u : (ι → ℝ) → ι → ℝ) (Pi.single a 1) b| ≤
                                  δ *
                                    RegularityStructures.parabolicSemigroup.scaleDist v u ^
                                      (𝒯.deg a - 𝒯.deg b)) →
                      ‖RegularityStructures.gammaSplitLeftBadTermDiff M₁ M₂ D i j x y z‖ₑ ≤
                        ∑ k ∈ RegularityStructures.gammaBadIntermediate 𝒯 D i j,
                          (ENNReal.ofReal
                                (δ *
                                  RegularityStructures.parabolicSemigroup.scaleDist y x ^
                                    (𝒯.deg i - 𝒯.deg k)) *
                              ENNReal.ofReal
                                (C *
                                  RegularityStructures.parabolicSemigroup.scaleDist z y ^
                                    (𝒯.deg k - 𝒯.deg j)) +
                            ENNReal.ofReal
                                (C *
                                  RegularityStructures.parabolicSemigroup.scaleDist y x ^
                                    (𝒯.deg i - 𝒯.deg k)) *
                              ENNReal.ofReal
                                (δ *
                                  RegularityStructures.parabolicSemigroup.scaleDist z y ^
                                    (𝒯.deg k - 𝒯.deg j))))
    (h_RegularityStructures_gammaDiffBad_ofReal_mul_rpow_scale_le : ∀ {C A B d e a b : ℝ} {r N l : ℕ},
      0 ≤ C →
        0 ≤ A →
          0 ≤ B →
            0 ≤ d →
              0 ≤ e →
                0 ≤ a →
                  0 ≤ b →
                    d ≤ A * (1 / 2 ^ N) →
                      e ≤ B * (1 / 2 ^ (N + l)) →
                        ENNReal.ofReal (C * d ^ a * e ^ b) ^ r ≤
                          ENNReal.ofReal (C * A ^ a * B ^ b) ^ r *
                              RegularityStructures.dyadicBase N ^ ((↑r : ℝ) * (a + b)) *
                            RegularityStructures.dyadicBase l ^ ((↑r : ℝ) * b))
    :
    gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
          4 ^ (𝒯.deg k - 𝒯.deg j)) *
          dyadicBase N ^ β * dyadicBase l ^ r := by
  classical
  unfold gammaDiffBadLeftAnnulusStepSup
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  by_cases hnear : parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) b) ≤
      20 / (2 : ℝ) ^ N
  · simp only [ite_eq_left hnear]
    have hgeom := h_RegularityStructures_gammaDiffBad_left_geometry S hbox N (N + l)
      (Nat.le_add_right N l) a b hnear
    have hbad := h_RegularityStructures_gammaSplitLeftBadTermDiff_enorm_le
      (M₁ ω) (M₂ ω) D γ C d hC hd i j
      (hsParabolicCellRepresentative S (N + l + 1) b)
      (hsParabolicCellRepresentative S (N + l + 1) a)
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) a)) hi hij
      (fun c e hde hci hej u v => hdet₁ c e hde hci hej ω u v)
      (fun c e hde hci hej u v => hdet₂ c e hde hci hej ω u v)
      (fun c e hde hci hej u v => hdiff c e hde hci hej ω u v)
    calc
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j, (
          ENNReal.ofReal (d * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l + 1) a)
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a))
            (hsParabolicCellRepresentative S (N + l + 1) a) ^
              (𝒯.deg k - 𝒯.deg j)) +
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l + 1) a)
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (d * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a))
            (hsParabolicCellRepresentative S (N + l + 1) a) ^
              (𝒯.deg k - 𝒯.deg j))) := hbad
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
          2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
            4 ^ (𝒯.deg k - 𝒯.deg j)) *
            dyadicBase N ^ β * dyadicBase l ^ r := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
        have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
        have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
        have hscale := h_RegularityStructures_gammaDiffBad_ofReal_mul_rpow_scale_le
          (C := C * d) (A := 24) (B := 4)
          (a := 𝒯.deg i - 𝒯.deg k)
          (b := 𝒯.deg k - 𝒯.deg j) (r := 1) (N := N) (l := l)
          (mul_nonneg hC hd) (by norm_num) (by norm_num)
          (parabolicNorm_nonneg _) (parabolicNorm_nonneg _)
          (by linarith) (by linarith)
          (by simpa [div_eq_mul_inv] using hgeom.1)
          (by simpa [div_eq_mul_inv] using hgeom.2)
        have hscale'' := hscale
        simp only [pow_one, Nat.cast_one, one_mul] at hscale''
        have hdegree : β = (𝒯.deg i - 𝒯.deg k) +
            (𝒯.deg k - 𝒯.deg j) := by rw [hβ]; ring
        have hfine : dyadicBase l ^ (𝒯.deg k - 𝒯.deg j) ≤
            dyadicBase l ^ r := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact hgap k hjk hki
        have hbase :
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ β * dyadicBase l ^
                (𝒯.deg k - 𝒯.deg j) =
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ ((𝒯.deg i - 𝒯.deg k) +
                (𝒯.deg k - 𝒯.deg j)) * dyadicBase l ^
                (𝒯.deg k - 𝒯.deg j) := by rw [hdegree]
        have hprod₁ :
            ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) a)
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) := by
          have hfirst : 0 ≤ d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) a)
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k) :=
            mul_nonneg hd (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
          rw [← ENNReal.ofReal_mul hfirst]
          congr 1
          ring_nf
        have hprod₂ :
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) a)
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) := by
          rw [← ENNReal.ofReal_mul]
          · congr 1
            ring
          · exact mul_nonneg hC (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
        have hone :
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) ≤
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ ((𝒯.deg i - 𝒯.deg k) +
                (𝒯.deg k - 𝒯.deg j)) * dyadicBase l ^
                (𝒯.deg k - 𝒯.deg j) := hscale''
        have hone' :
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) ≤
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ β * dyadicBase l ^ r := by
          calc
            _ ≤ ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) *
                dyadicBase N ^ ((𝒯.deg i - 𝒯.deg k) +
                  (𝒯.deg k - 𝒯.deg j)) * dyadicBase l ^
                  (𝒯.deg k - 𝒯.deg j) := hone
            _ = ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ (𝒯.deg k - 𝒯.deg j) := hbase.symm
            _ ≤ _ := by gcongr
        calc
          _ ≤ (ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ r) +
              (ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ r) := add_le_add
            (hprod₁ ▸ (hone' : _)) (hprod₂ ▸ (hone' : _))
          _ = 2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ r := by ring
  · simp only [ite_eq_right hnear]
    exact bot_le

end RegularityStructures
end
