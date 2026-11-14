module

public import Mathlib
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Moments.CovarianceBilinDual
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.L2Space

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v10c743e08bf2.Common.Mathlib.Probability.Distributions.Gaussian.CompletionResultsToBeMoved ====
public section
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
/-
Copyright (c) 2025 Rémy Degenne, 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Matteo Cipollina
-/
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
/-!
# Completion results (vendored)

Closure extension of continuous linear maps on submodules. Adapted from Rémy Degenne, mathlib4
[#26291](https://github.com/leanprover-community/mathlib4/pull/26291) and
[#30582](https://github.com/leanprover-community/mathlib4/pull/30582) (both open as of 2026-01).
-/
@[expose] public section
open NormedSpace UniformSpace
open scoped _root_.InnerProductSpace
-- `ContinuousConstSMul` does not always get inferred automatically for submodules;
-- we register the subtype instance we need for this vendored development.
set_option linter.unusedVariables false in
axiom _root_.ColeHopfFoundation.instContinuousConstSMul_submodule.{w_u_1,w_u_2} : ∀ {M : Type w_u_1} {R : Type w_u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M]
  [inst_2 : Module R M] [inst_3 : TopologicalSpace M] [ContinuousConstSMul R M] (s : Submodule R M),
  ContinuousConstSMul R ↥s
attribute [instance] _root_.ColeHopfFoundation.instContinuousConstSMul_submodule

/-- Coercion from a submodule to its topological closure. -/
def coeClosure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    s → s.topologicalClosure := fun x =>
  ⟨x.1, (Submodule.le_topologicalClosure s) x.2⟩
-- This coercion existed upstream; we reintroduce it for the vendored development.
instance coeTC_submodule_topologicalClosure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R
    M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) : CoeTC s s.topologicalClosure :=
  ⟨coeClosure s⟩

@[simp] axiom coeClosure_add {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) (x y : s) :
    coeClosure s (x + y) = coeClosure s x + coeClosure s y
@[simp] axiom coeClosure_smul {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
    (s : Submodule R M) (c : R) (x : s) :
    coeClosure s (c • x) = c • coeClosure s x
/-- Coercion from a submodule to its topological closure as a continuous linear map. -/
def coeClosureCLM {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    s →L[R] s.topologicalClosure where
  toFun := coeClosure s
  map_add' := coeClosure_add s
  map_smul' := coeClosure_smul s
  cont := by
    -- continuity is inherited from the subtype map into `M`
    convert (continuous_subtype_val.subtype_mk
        fun x : s => (Submodule.le_topologicalClosure s) x.2) using 1
    ext x
    rfl

section Extension
variable {M R F : Type*} [Ring R] [NormedAddCommGroup M] [Module R M]
  [UniformContinuousConstSMul R M] [ContinuousConstSMul R M]
  [UniformSpace F] [AddCommGroup F] [Module R F] [T2Space F] [CompleteSpace F]
  [IsUniformAddGroup F] [UniformContinuousConstSMul R F] [ContinuousConstSMul R F]
  {s : Submodule R M}
/-- Extension of a linear map `s →L[R] F` on a submodule to a linear map on the topological
closure of the submodule. -/
noncomputable
def closureExtensionCLM (s : Submodule R M) (f : s →L[R] F) : s.topologicalClosure →L[R] F :=
  ContinuousLinearMap.extend f (coeClosureCLM s)

end Extension
end
end ColeHopfFoundation

end
end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v10c743e08bf2.Common.Mathlib.Probability.Distributions.Gaussian.CameronMartin ====
public section
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
/-
Copyright (c) 2025 Rémy Degenne, 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Matteo Cipollina
-/
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory
/-!
# Cameron–Martin space

Hilbert space associated to a finite-second-moment Borel measure `μ` on a real Banach space `E`:
closure of the range of `StrongDual.centeredToLp μ` in `Lp ℝ 2 μ`. Main: `cameronMartin`, `cmCoe`,
`cmOfBounded`. Bogachev, *Gaussian Measures*; Kuo, LNM 463.

Adapted from Rémy Degenne, mathlib4
[#26291](https://github.com/leanprover-community/mathlib4/pull/26291) (`HasTwoMoments`:
[#27608](https://github.com/leanprover-community/mathlib4/pull/27608)); both open as of 2026-01.
-/
--@[expose] public section
open MeasureTheory ProbabilityTheory NormedSpace UniformSpace
open scoped _root_.MeasureTheory _root_.ProbabilityTheory _root_.ENNReal _root_.NNReal _root_.Real _root_.Topology _root_.InnerProductSpace
variable {M R F : Type*} [Ring R] [NormedAddCommGroup M] [Module R M]
    [CompleteSpace M] [UniformContinuousConstSMul R M]
    [UniformSpace F] [AddCommGroup F] [Module R F] [T2Space F] [CompleteSpace F]
    {s : Submodule R M}
namespace ProbabilityTheory
/-- Finite measure `μ` with `MemLp id 2 μ`. -/
class HasTwoMoments {E : Type*} {_ : MeasurableSpace E} [ENorm E] [TopologicalSpace E]
    (μ : Measure E) extends IsFiniteMeasure μ where
  memLp_two : MemLp id 2 μ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E]
  {μ : Measure E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {y : E}
set_option linter.unusedVariables false in
axiom _root_.ColeHopfFoundation.ProbabilityTheory.instHasTwoMomentsOfSecondCountableTopologyOfIsGaussian.{w_u_4} : ∀ {E : Type w_u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {μ : MeasureTheory.Measure E}
  [SecondCountableTopology E] [ProbabilityTheory.IsGaussian μ],
  ColeHopfFoundation.ProbabilityTheory.HasTwoMoments μ
attribute [instance] _root_.ColeHopfFoundation.ProbabilityTheory.instHasTwoMomentsOfSecondCountableTopologyOfIsGaussian

/-! ### Centered dual embedding `StrongDual.centeredToLp` -/
namespace StrongDual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] {μ : Measure E}
-- Needed to use `StrongDual.toLp μ 2`.
set_option linter.unusedVariables false in
axiom _root_.ColeHopfFoundation.ProbabilityTheory.StrongDual.instFact_one_le_two : Fact (1 ≤ 2)
attribute [instance] _root_.ColeHopfFoundation.ProbabilityTheory.StrongDual.instFact_one_le_two
/-- Centered dual embedding `L ↦ (x ↦ L(x - μ[id]))` into `Lp ℝ 2 μ`. -/
noncomputable
def centeredToLp (μ : Measure E) [IsFiniteMeasure μ] :
    _root_.StrongDual ℝ E →L[ℝ] Lp ℝ 2 μ :=
  (_root_.StrongDual.toLp μ 2) -
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.apply ℝ ℝ (∫ x : E, x ∂μ))
      (Lp.const 2 μ (1 : ℝ)))

end StrongDual
section CameronMartinSpace
/-- Closure of the range of `StrongDual.centeredToLp μ` in `Lp ℝ 2 μ`. -/
noncomputable abbrev cameronMartin (μ : Measure E) [HasTwoMoments μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap).topologicalClosure
variable [HasTwoMoments μ]

noncomputable
instance instCoeFun : CoeFun (cameronMartin μ) (fun _ ↦ E → ℝ) := ⟨fun f ↦ (f : E → ℝ)⟩

/-- Inclusion from the StrongDual into the Cameron-Martin space, as a linear map. -/
noncomputable
def cmOfDual (μ : Measure E) [HasTwoMoments μ] : StrongDual ℝ E →ₗ[ℝ] cameronMartin μ :=
  (coeClosureCLM _).toLinearMap.comp ((StrongDual.centeredToLp (E := E)
    μ).toLinearMap.rangeRestrict)
noncomputable
instance : Coe (StrongDual ℝ E) (cameronMartin μ) := ⟨cmOfDual μ⟩

end CameronMartinSpace
section cmOfBounded
/-! ## Map from bounded Cameron–Martin-norm points -/
variable [HasTwoMoments μ]
namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas
/-- Evaluate `x` in the range of `centeredToLp μ` at `y : E`, via a preimage dual functional. -/
noncomputable
def evalL2 (μ : Measure E) [HasTwoMoments μ] (y : E)
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) : ℝ :=
  (LinearMap.mem_range.mp x.2).choose y

axiom norm_evalL2_le (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) :
    ‖evalL2 μ y x‖ ≤ ‖x‖ * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y

axiom evalL2_eq (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap)
    {L : StrongDual ℝ E}
    (hL : StrongDual.centeredToLp (E := E) μ L = (x : Lp ℝ 2 μ)) :
    evalL2 μ y x = L y

end CameronMartinAux
open CameronMartinAux
/-- Evaluation on `cameronMartin μ` at `y` of bounded Cameron–Martin norm; `cmEval μ y hy (cmOfDual
μ L) = L y`. -/
noncomputable
def cmEval (μ : Measure E) [HasTwoMoments μ] (y : E)
    (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    StrongDual ℝ (cameronMartin μ) :=
  closureExtensionCLM (LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) <|
  LinearMap.mkContinuous
    { toFun x := evalL2 μ y x
      map_add' x₁ x₂ := by
        obtain ⟨L₁, hL₁⟩ := LinearMap.mem_range.mp x₁.2
        obtain ⟨L₂, hL₂⟩ := LinearMap.mem_range.mp x₂.2
        rw [evalL2_eq hy x₁ hL₁, evalL2_eq hy x₂ hL₂, evalL2_eq hy (x₁ + x₂) (L := L₁ + L₂)]
        · simp
        · have hL₁' : StrongDual.centeredToLp (E := E) μ L₁ = (x₁ : Lp ℝ 2 μ) := by
            simpa using hL₁
          have hL₂' : StrongDual.centeredToLp (E := E) μ L₂ = (x₂ : Lp ℝ 2 μ) := by
            simpa using hL₂
          calc
            StrongDual.centeredToLp (E := E) μ (L₁ + L₂)
                = StrongDual.centeredToLp (E := E) μ L₁ + StrongDual.centeredToLp (E := E) μ L₂ :=
                  by
                    simp
            _ = (x₁ : Lp ℝ 2 μ) + (x₂ : Lp ℝ 2 μ) := by simp [hL₁', hL₂']
            _ = (x₁ + x₂ : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) := rfl
      map_smul' r x := by
        obtain ⟨L, hL⟩ := LinearMap.mem_range.mp x.2
        rw [evalL2_eq hy x hL, evalL2_eq hy (r • x) (L := r • L)]
        · simp
        · have hL' : StrongDual.centeredToLp (E := E) μ L = (x : Lp ℝ 2 μ) := by
            simpa using hL
          calc
            StrongDual.centeredToLp (E := E) μ (r • L) = r • StrongDual.centeredToLp (E := E) μ L :=
              by
              simp
            _ = r • (x : Lp ℝ 2 μ) := by simp [hL']
            _ = (r • x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) := rfl }
    (⨆ (L' : StrongDual ℝ E) (_ : Var[L'; μ] ≤ 1), L' y) fun x ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [mul_comm]
    exact norm_evalL2_le hy x

variable [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]

end cmOfBounded
section CmCoe
/-! ## `cmCoe`: embedding into `E` -/
variable [SecondCountableTopology E] [HasTwoMoments μ]
namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas
/-- Auxiliary Bochner integral reconstructing a point of `E` from `x` in the range of `centeredToLp
μ`. -/
noncomputable
def toInit (μ : Measure E) [IsFiniteMeasure μ]
    (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) : E :=
  ∫ y, (LinearMap.mem_range.mp x.2).choose (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ

axiom apply_toInit_eq_inner (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap)
    (L : StrongDual ℝ E) :
    L (toInit μ x) = ⟪StrongDual.centeredToLp (E := E) μ L, x⟫_ℝ
axiom norm_toInit_le (x : LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) :
    ‖toInit μ x‖ ≤ ‖StrongDual.centeredToLp (E := E) μ‖ * ‖x‖
end CameronMartinAux
open CameronMartinAux
/-- Injective embedding `cameronMartin μ →L[ℝ] E`. -/
noncomputable
def cmCoe {μ : Measure E} [HasTwoMoments μ] : cameronMartin μ →L[ℝ] E :=
  closureExtensionCLM (LinearMap.range (StrongDual.centeredToLp (E := E) μ).toLinearMap) <|
  LinearMap.mkContinuous
    { toFun x := toInit μ x
      map_add' x y := by
        refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_add, apply_toInit_eq_inner, Submodule.coe_add, inner_add_right]
      map_smul' r x := by
        refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_smul, apply_toInit_eq_inner, Submodule.coe_smul, inner_smul_right]
        simp }
    ‖StrongDual.centeredToLp (E := E) μ‖ norm_toInit_le

end CmCoe
variable [SecondCountableTopology E] [HasTwoMoments μ]
  [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]

end ProbabilityTheory
end ColeHopfFoundation

end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v10c743e08bf2.Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBP ====
public section
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory
/-!
# Cameron–Martin IBP scaffold

Measure-level identity: `∫ F(y + cmCoe (t • x)) dμ = ∫ exp((t•x) y - ‖t•x‖²/2) * F(y) dμ`
for `x : cameronMartin μ`. Differentiate at `t = 0` for Gaussian IBP.
-/
open MeasureTheory Filter
open ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.Topology _root_.InnerProductSpace
namespace ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]
/-! ## Tilt = shift for Bochner integrals (real-valued) -/
/-- The shifted integral functional \(t \mapsto \int F(y + \mathrm{cmCoe}(t\cdot x))\,d\mu\). -/
noncomputable def cameronMartinShiftFun (x : cameronMartin μ) (F : E → ℝ) (t : ℝ) : ℝ :=
  ∫ y, F (y + cmCoe (t • x)) ∂μ
end ProbabilityTheory
end ColeHopfFoundation

end
end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v10c743e08bf2.Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique ====
public section
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory
/-!
# Fernique consequences

For a Gaussian measure `μ` on a second-countable Banach space, `x ↦ exp(C ‖x‖²)` is integrable
for some `C > 0`. Main: exponential-square integrability of continuous linear functionals.
-/
open MeasureTheory ProbabilityTheory
open scoped _root_.ENNReal _root_.Real _root_.Topology
namespace ProbabilityTheory
namespace IsGaussian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [ProbabilityTheory.IsGaussian μ]

/-- Polynomial growth domination helper: `(1 + ‖x‖)^n` is integrable for all `n`. -/
axiom integrable_one_add_norm_pow (n : ℕ) :
    Integrable (fun x : E => (1 + ‖x‖) ^ n) μ
end IsGaussian
end ProbabilityTheory
end ColeHopfFoundation

end
end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Examples.Example_26ab1e9e27bcbb2ead73_CameronMartinIBPAnalytic ====
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
/- Compatibility adaptation: direct extensional simplification where modern elaboration closes conversion goals automatically. -/
set_option autoImplicit false
@[expose] public section
/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory
/-!
# Cameron–Martin IBP: analytic layer

Differentiate `t ↦ ∫ F(y) · exp(t⟨x,y⟩ - t²‖x‖²/2) dμ` at `t = 0`. Main:
`cameronMartinTiltKernel_aeEq_tiltKernel`, `hasDerivAt_tiltFun_at0_of_bounded`,
`hasDerivAt_tiltFun_at0_of_integrable_profile`.
-/
open MeasureTheory Filter
open scoped _root_.Topology _root_.Real _root_.ENNReal _root_.NNReal
namespace ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]
namespace CameronMartinIBPAnalytic
section ShiftFun
variable (F : E → ℝ)

end ShiftFun

/-- Differentiate the Cameron–Martin shift functional at `t = 0` under a local domination
hypothesis. -/
axiom hasDerivAt_shiftFun_at0_of_integrable_bound
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ y ∂μ,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0
theorem hasDerivAt_shiftFun_at0_polyGrowth
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ y, |F y| ≤ C * (1 + ‖y‖) ^ m)
    (hF'_growth : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ m) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  have hbase : Integrable (fun y : E => (1 + ‖y‖) ^ m) μ :=
    ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := μ) m
  have hF_int : Integrable F μ :=
    (hbase.const_mul C).mono' hF_meas.aestronglyMeasurable <|
      ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hF_growth y)
  let v : E := cmCoe x
  let bound : E → ℝ := fun y => (C * ‖v‖ * (1 + ‖v‖) ^ m) * (1 + ‖y‖) ^ m
  have hbound_int : Integrable bound μ :=
    hbase.const_mul (C * ‖v‖ * (1 + ‖v‖) ^ m)
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) (1 : ℝ),
      ‖(fderiv ℝ F (y + t • v)) v‖ ≤ bound y := by
    refine ae_of_all _ (fun y t ht => ?_)
    have ht1 : ‖t‖ ≤ (1 : ℝ) := le_of_lt (by simpa [Metric.mem_ball, Real.norm_eq_abs] using ht)
    have hnorm : ‖y + t • v‖ ≤ ‖y‖ + ‖v‖ := by
      have : ‖t • v‖ ≤ ‖v‖ := by simpa [norm_smul] using mul_le_mul_of_nonneg_right ht1 (norm_nonneg
        v)
      have htmp : ‖y‖ + ‖t • v‖ ≤ ‖y‖ + ‖v‖ := by
        simpa [add_comm] using add_le_add_right this ‖y‖
      exact (norm_add_le _ _).trans htmp
    have hle : 1 + ‖y + t • v‖ ≤ (1 + ‖v‖) * (1 + ‖y‖) := by
      have h1 : (1 : ℝ) + ‖y + t • v‖ ≤ (1 : ℝ) + (‖y‖ + ‖v‖) := by
        simpa [add_assoc, add_left_comm, add_comm] using (add_le_add_left hnorm 1)
      have h2 : (1 : ℝ) + (‖y‖ + ‖v‖) ≤ (1 + ‖v‖) * (1 + ‖y‖) := by
        nlinarith [norm_nonneg y, norm_nonneg v]
      exact h1.trans h2
    have hp : (1 + ‖y + t • v‖) ^ m ≤ ((1 + ‖v‖) * (1 + ‖y‖)) ^ m :=
      pow_le_pow_left₀ (by positivity) hle m
    have hOp := (fderiv ℝ F (y + t • v)).le_opNorm v
    have hB : ‖fderiv ℝ F (y + t • v)‖ ≤ C * (1 + ‖y + t • v‖) ^ m := hF'_growth (y + t • v)
    calc
      ‖(fderiv ℝ F (y + t • v)) v‖ ≤ ‖fderiv ℝ F (y + t • v)‖ * ‖v‖ := hOp
      _ ≤ (C * (1 + ‖y + t • v‖) ^ m) * ‖v‖ := by gcongr
      _ ≤ (C * ((1 + ‖v‖) * (1 + ‖y‖)) ^ m) * ‖v‖ := by gcongr
      _ = bound y := by
          simp [bound, mul_pow]
          ring
  simpa using
    hasDerivAt_shiftFun_at0_of_integrable_bound (μ := μ) x F hF_meas hF_c1 (δ := (1 : ℝ))
      (by norm_num) hF_int bound hbound_int hbound
/-
### Tilt functional: helper lemmas
-/
end CameronMartinIBPAnalytic
open CameronMartinIBPAnalytic
end ProbabilityTheory
end ColeHopfFoundation
