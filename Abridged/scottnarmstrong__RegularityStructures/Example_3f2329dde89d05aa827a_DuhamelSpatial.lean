module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Order.Interval.Set.Pi
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Torus.Basic ====
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
# The three-torus and space-time

We write `T³ = ℝ³/ℤ³` as `UnitAddTorus (Fin 3)` and space-time `ℝ × T³` as a product. Points of
`ℝ³` are functions `Fin 3 → ℝ`, with the Euclidean square norm written out by hand. A function on
the torus is smooth if its periodic lift to `ℝ³` is smooth.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open scoped ContDiff
namespace RegularityStructures
/-- The three-torus `T³ = ℝ³/ℤ³`. -/
abbrev Torus3 : Type := UnitAddTorus (Fin 3)
def torusProj (y : Fin 3 → ℝ) : Torus3 := fun i => ((y i : ℝ) : UnitAddCircle)
/-- The representative of a point of `T³` in `[0, 1)³`. -/
def torusRep (x : Torus3) : Fin 3 → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)
/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Torus.HeatKernel ====
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
# Heat kernels on the three-torus

* `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`, the heat kernel on `ℝ³`;
* `heatKernel t`, its periodisation `p_t` on `T³` (the statement, equation (2.1));
* `heatSemigroup s f`, the heat semigroup `P_s` acting on `C(T³)` by convolution with the Gaussian
  on `ℝ³`;
* `massiveHeatKernel`, the kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` of `(∂_t - Δ + 1)⁻¹`
  (equation (2.2)).

The lemmas show that `gaussKernel s` is a probability density for `s > 0`, so `P_s` is linear
and contracts the supremum norm.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open MeasureTheory Real
namespace RegularityStructures
/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) * exp (-sqNorm3 y / (4 * t))
end RegularityStructures
end
/-! ### The Gaussian density on `ℝ³` -/
public section
open MeasureTheory Real
namespace RegularityStructures

/-! ### The heat semigroup -/
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.TorusLift ====
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
# Lifting functions between `T³` and `ℝ³`

The projection `torusProj : ℝ³ → T³` is a continuous additive open quotient map that does not
increase distances. A continuous function on `ℝ³` that is constant on the fibres of `torusProj`
descends to a continuous function on `T³` (`torusDescend`). Derivatives of functions on `T³` are
those of their periodic lifts (`HasTorusDeriv`). Finally `torusShift a` is the translation
`g ↦ g(· + a)` on `C(T³, E)`, as a continuous linear map.

These are the bookkeeping tools of the semilinear heat theory in `RegularityStructures/PDE/`.
-/
@[expose] public noncomputable section
open Set
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end RegularityStructures.PDE
end
public section
open Set Filter Topology
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-! ### The projection `ℝ³ → T³` -/

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.PDE.torusProj_eq_iff_sub : ∀ (a b : Fin 3 → ℝ),
  RegularityStructures.torusProj a = RegularityStructures.torusProj b ↔
    RegularityStructures.torusProj (a - b) = 0
end RegularityStructures.PDE
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.HeatOp ====
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
# The heat operator on `C(T³, E)`

For a Banach space `E`, `t ∈ ℝ` and `g ∈ C(T³, E)`,
`heatOp t g x = ∫_{ℝ³} γ₁(z) g(x - √t z) dz`, where `γ₁ = gaussKernel 1` is the unit-time heat
kernel on `ℝ³`. For `t > 0` this is the heat semigroup `P_t g(x) = ∫ γ_t(y) g(x - y) dy` after the
substitution `y = √t z`. For `t ≤ 0` the square root vanishes and `heatOp t g = g`.

Writing the operator with the unit Gaussian makes the dependence on `t` sit inside the argument of
`g`, so continuity in `(t, x)`, up to and including `t = 0`, is one application of dominated
convergence.

## Main results

* `norm_heatOp_le`: `P_t` contracts the supremum norm;
* `heatOpCLM`: `P_t` as a continuous linear map;
* `continuous_heatOp`: `(t, g) ↦ P_t g` is jointly continuous, so `t ↦ P_t g` is a continuous path
  in `C(T³, E)` with `P_0 g = g`;
* `heatOp_torusShift`, `heatOp_compLeftContinuous`: `P_t` commutes with translations and with
  continuous linear maps of the values.
-/
open MeasureTheory Real Filter Topology
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
/-! ### The unit Gaussian -/
public section

/-! ### The integrand -/

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.PDE.continuous_heatOpFun.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  (g : C(RegularityStructures.Torus3, E)),
  Continuous fun (p : ℝ × RegularityStructures.Torus3) ↦
    ∫ (z : Fin 3 → ℝ),
      RegularityStructures.gaussKernel 1 z •
        (g : RegularityStructures.Torus3 → E) (p.2 - RegularityStructures.torusProj (√p.1 • z))
end
/-! ### The operator -/
@[expose] public noncomputable section
/-- The heat operator `P_t g(x) = ∫_{ℝ³} γ₁(z) g(x - √t z) dz` on `C(T³, E)`. It is the heat
semigroup for `t > 0` and the identity for `t ≤ 0`. -/
def heatOp (t : ℝ) (g : C(Torus3, E)) : C(Torus3, E) where
  toFun x := ∫ z : Fin 3 → ℝ, gaussKernel 1 z • g (x - torusProj (√t • z))
  continuous_toFun :=
    (continuous_heatOpFun g).comp (Continuous.prodMk continuous_const continuous_id)
end
public section

variable [CompleteSpace E]
end
@[expose] public noncomputable section
variable [CompleteSpace E]
end
public section

/-! ### Commutation with translations and with linear maps of the values -/
variable [CompleteSpace E] [CompleteSpace F]
end
end RegularityStructures.PDE

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.Duhamel ====
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
# The Duhamel integral

For a continuous path `h : ℝ → C(T³, E)`,
`duhamel h t = ∫₀ᵗ P_{t-s} h(s) ds`, a Bochner integral in the Banach space `C(T³, E)`. This is the
solution operator of the inhomogeneous heat equation `∂_t v = Δv + h`, `v(0) = 0`, in mild form.

## Main results

* `continuous_duhamel`: `t ↦ duhamel h t` is continuous;
* `duhamel_apply`: the integral may be evaluated pointwise in `x`;
* `norm_duhamel_le`: `‖duhamel h t‖ ≤ ∫₀ᵗ ‖h s‖ ds`;
* linearity in `h`, commutation with translations and with linear maps of the values;
* `duhamel_congr`: `duhamel h t` only depends on `h` on `[0, t]`.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The Duhamel integral `∫₀ᵗ P_{t-s} h(s) ds` in `C(T³, E)`. -/
def duhamel (h : ℝ → C(Torus3, E)) (t : ℝ) : C(Torus3, E) :=
  ∫ s in (0 : ℝ)..t, heatOp (t - s) (h s)
end RegularityStructures.PDE
end
public section
open MeasureTheory Set Filter Topology
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

variable [CompleteSpace E] [CompleteSpace F]
end RegularityStructures.PDE
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.Mild ====
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
# Mild solutions of semilinear heat equations on `T³`

For a continuous nonlinearity `G : ℝ × T³ × E → E` and `u₀ ∈ C(T³, E)`, a path
`u : ℝ → C(T³, E)` is a mild solution of `∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]` if
`u(t) = P_t u₀ + ∫₀ᵗ P_{t-s} G(s, ·, u(s)) ds` for `t ∈ [0, T]`.

## Main results

* `IsMildSolution.eqOn`: two continuous mild solutions agree on `[0, T]` when `G` is Lipschitz in
  `u` (Grönwall);
* `exists_isMildSolution`: a continuous mild solution exists on `[0, T]` when `G` is globally
  Lipschitz in `u` for `t ∈ [0, T]` (Banach's fixed point theorem in the weighted norm
  `sup_t e^{-λt} ‖u(t)‖`, which makes the Picard map a contraction on the whole interval).
-/
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The Nemytskii operator `v ↦ G(s, ·, v(·))` on `C(T³, E)`. -/
def nemytskii (G : C(ℝ × Torus3 × E, E)) (s : ℝ) (v : C(Torus3, E)) : C(Torus3, E) :=
  ⟨fun x => G (s, x, v x), by fun_prop⟩
end RegularityStructures.PDE
end
public section
open MeasureTheory Set Filter Topology Real
open scoped NNReal
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
section Nemytskii
omit [NormedSpace ℝ E]

end Nemytskii
section Existence
variable (G : C(ℝ × Torus3 × E, E)) (u₀ : C(Torus3, E)) {T : ℝ} (hT : 0 ≤ T) (lam : ℝ)
end Existence
end RegularityStructures.PDE
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.Nonlin ====
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
# Smooth nonlinearities and their jets

A nonlinearity `G : ℝ × T³ × F → F` is smooth when its lift
`nonlinLift G (s, y, v) = G(s, torusProj y, v)` is smooth on `ℝ × ℝ³ × F`. Its derivative in
`(x, u)` descends to a continuous map `nonlinDeriv G` on `ℝ × T³ × F`.

* `hasTorusDeriv_nemytskii`: the chain rule for `x ↦ G(s, x, v(x))`;
* `jetNonlin G`: the nonlinearity `(s, x, v, ω) ↦ (G(s, x, v), (D G(s, x, v)(eᵢ, ωᵢ))ᵢ)` of the
  system satisfied by a solution together with its first partial derivatives;
* `contDiff_nonlinLift_jetNonlin`: the jet nonlinearity of a smooth nonlinearity is smooth.
-/
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
def descend3 (h : ℝ × (Fin 3 → ℝ) × F → X) (hc : Continuous h)
    (hp : ∀ s a b v, torusProj a = torusProj b → h (s, a, v) = h (s, b, v)) :
    C(ℝ × Torus3 × F, X) where
  toFun p := h (p.1, torusRep p.2.1, p.2.2)
  continuous_toFun := by
    have hq : IsOpenQuotientMap (Prod.map (id : ℝ → ℝ) (Prod.map torusProj (id : F → F))) :=
      IsOpenQuotientMap.id.prodMap ((IsOpenQuotientMap.piMap fun _ =>
        QuotientAddGroup.isOpenQuotientMap_mk).prodMap IsOpenQuotientMap.id)
    rw [hq.isQuotientMap.continuous_iff]
    refine hc.congr fun p => ?_
    refine (hp _ _ _ _ ?_).symm
    funext i
    simp [torusProj, torusRep]
end RegularityStructures.PDE
end
public section
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end
public section
open Set Filter Topology
namespace RegularityStructures.PDE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end RegularityStructures.PDE
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.Analysis.Parabolic.Basic ====
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
end RegularityStructures
end
public section
namespace RegularityStructures
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.Phi43.Inhomogeneity.DuhamelField ====
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
# The Duhamel field of a smooth periodic forcing

For a smooth spatially periodic `g : ℝ × ℝ³ → ℝ` (`PerSmooth g`), the Duhamel field
`duhamelField hg (t, y) = ∫₀ᵗ P_{t-r} g(r, ·) dr (y)` for `t > 0` (and `0` for `t ≤ 0`) is the mild
solution of `∂_t u = Δu + g`, `u(0) = 0` (`isMildSolution_duhamelPath`).  By the mild-solution
theory of `PDE/` it is smooth on `{t > 0}` (`smoothPos_duhamelField`).

This is the function `θ_s(t) = ∫_s^t P_{t-r} ζ(r) dr` of the restart datum of the `Φ⁴₃` fixed point
(with the time `t - s` as the first coordinate).
-/
open scoped ContDiff
@[expose] public noncomputable section
namespace RegularityStructures.Inhomogeneity
open RegularityStructures.PDE
/-- A smooth function on `ℝ × ℝ³`, periodic in the space variables (the lift of a smooth function
on `ℝ × T³`). -/
structure PerSmooth (g : ParabolicSpace → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  periodic : ∀ (z : ParabolicSpace) (c : Fin 3 → ℝ), torusProj c = 0 → g (z.1, z.2 + c) = g z
variable {g : ParabolicSpace → ℝ}
/-- The forcing `G(t, x, v) = g(t, x)` as a continuous function on `ℝ × T³ × ℝ`. -/
def forcing (hg : PerSmooth g) : C(ℝ × Torus3 × ℝ, ℝ) :=
  descend3 (fun p : ℝ × (Fin 3 → ℝ) × ℝ => g (p.1, p.2.1))
    (hg.smooth.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
    (fun s a b v hab => by
      have hc : torusProj (b - a) = 0 := (torusProj_eq_iff_sub b a).1 hab.symm
      have := hg.periodic (s, a) (b - a) hc
      simpa using this.symm)
/-- The path `s ↦ g(s, ·) ∈ C(T³)`. -/
def forcePath (hg : PerSmooth g) (s : ℝ) : C(Torus3, ℝ) :=
  nemytskii (forcing hg) s 0
/-- The Duhamel field `(t, y) ↦ ∫₀ᵗ P_{t-r} g(r, ·) dr (y)` for `t > 0`, and `0` for `t ≤ 0`. -/
def duhamelField (hg : PerSmooth g) : ParabolicSpace → ℝ :=
  fun z => if 0 < z.1 then duhamel (forcePath hg) z.1 (torusProj z.2) else 0
end RegularityStructures.Inhomogeneity
end
public section
open scoped ContDiff
namespace RegularityStructures.Inhomogeneity
open RegularityStructures.PDE Set Filter Topology
variable {g : ParabolicSpace → ℝ}

end RegularityStructures.Inhomogeneity
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_3f2329dde89d05aa827a_DuhamelSpatial ====
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
# Spatial derivatives of the Duhamel field

For `g` smooth and spatially periodic, `∂_j (duhamelField g) = duhamelField (∂_j g)` on `{t > 0}`
(`pd_succ_duhamelField`): the spatial derivative falls on the forcing
(`hasTorusDeriv_duhamel`).  Iterating, every spatial derivative of the Duhamel field is the
Duhamel field of the corresponding derivative of the forcing (`pdWord_duhamelField`), and so is
bounded by `t` times the corresponding sup norm of the derivative of the forcing
(`abs_duhamelField_le`).
-/
open scoped ContDiff
@[expose] public noncomputable section
namespace RegularityStructures.Inhomogeneity
open RegularityStructures.PDE
variable {g : ParabolicSpace → ℝ}

set_option linter.unusedVariables false in
/-- **Sup bound of the Duhamel field**: `|duhamelField g (t, y)| ≤ M t` if `|g| ≤ M` on
`[0, t] × ℝ³`. -/
theorem abs_duhamelField_le (hg : PerSmooth g) {t M : ℝ}
    (hM : ∀ s ∈ Set.Icc 0 t, ∀ y, |g (s, y)| ≤ M) (ht : 0 < t) (y : Fin 3 → ℝ) 
    (h_RegularityStructures_Inhomogeneity_continuous_forcePath : ∀ {g : RegularityStructures.ParabolicSpace → ℝ}
      (hg : RegularityStructures.Inhomogeneity.PerSmooth g),
      Continuous (RegularityStructures.Inhomogeneity.forcePath hg))
    (h_RegularityStructures_Inhomogeneity_norm_forcePath_le : ∀ {g : RegularityStructures.ParabolicSpace → ℝ}
      (hg : RegularityStructures.Inhomogeneity.PerSmooth g) {t M : ℝ},
      (∀ s ∈ Set.Icc 0 t, ∀ (y : Fin 3 → ℝ), |g (s, y)| ≤ M) →
        0 ≤ t → ∀ s ∈ Set.Icc 0 t, ‖RegularityStructures.Inhomogeneity.forcePath hg s‖ ≤ M)
    (h_RegularityStructures_PDE_norm_duhamel_le_mul : ∀ {E : Type} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
      {h : ℝ → C(RegularityStructures.Torus3, E)},
      Continuous h →
        ∀ {t M : ℝ},
          0 ≤ t → (∀ s ∈ Set.Icc 0 t, ‖h s‖ ≤ M) → ‖RegularityStructures.PDE.duhamel h t‖ ≤ M * t)
    (h_RegularityStructures_Inhomogeneity_duhamelField_of_pos : ∀ {g : RegularityStructures.ParabolicSpace → ℝ}
      (hg : RegularityStructures.Inhomogeneity.PerSmooth g) {z : RegularityStructures.ParabolicSpace},
      0 < z.1 →
        RegularityStructures.Inhomogeneity.duhamelField hg z =
          (RegularityStructures.PDE.duhamel (RegularityStructures.Inhomogeneity.forcePath hg) z.1 :
              RegularityStructures.Torus3 → ℝ)
            (RegularityStructures.torusProj z.2))
    :
    |duhamelField hg (t, y)| ≤ M * t := by
  rw [h_RegularityStructures_Inhomogeneity_duhamelField_of_pos hg ht]
  have h := h_RegularityStructures_PDE_norm_duhamel_le_mul (h_RegularityStructures_Inhomogeneity_continuous_forcePath hg) ht.le (h_RegularityStructures_Inhomogeneity_norm_forcePath_le hg hM ht.le)
  exact (Real.norm_eq_abs _ ▸ (ContinuousMap.norm_coe_le_norm _ (torusProj y))).trans h
end RegularityStructures.Inhomogeneity
