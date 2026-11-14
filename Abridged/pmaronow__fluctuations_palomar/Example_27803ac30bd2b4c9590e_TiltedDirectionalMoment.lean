module

public import Mathlib

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.ParameterSpace ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/ParameterSpace.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
@[reducible] def ParameterSpace : ℕ → Type
  | 0 => ℝ
  | n+1 => ParameterSpace n × ℝ
instance parameterNormedGroup : (n : ℕ) → NormedAddCommGroup (ParameterSpace n)
  | 0 => inferInstanceAs (NormedAddCommGroup ℝ)
  | n+1 => letI := parameterNormedGroup n; inferInstanceAs (NormedAddCommGroup (ParameterSpace n × ℝ))
instance parameterNormedSpace : (n : ℕ) → NormedSpace ℝ (ParameterSpace n)
  | 0 => inferInstanceAs (NormedSpace ℝ ℝ)
  | n+1 => letI := parameterNormedSpace n; inferInstanceAs (NormedSpace ℝ (ParameterSpace n × ℝ))

end SK.Analytic
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.CubeMeasures ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/CubeMeasures.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
instance parameterMeasurable : (n : ℕ) → MeasurableSpace (ParameterSpace n)
  | 0 => inferInstanceAs (MeasurableSpace ℝ)
  | n+1 => letI := parameterMeasurable n; inferInstanceAs (MeasurableSpace (ParameterSpace n × ℝ))

end SK.Analytic
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianDomination ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/GaussianDomination.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
def HasExpGrowth {E F : Type} [Norm E] [Norm F] (f : E → F) : Prop :=
  ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ C*Real.exp (M*‖x‖)

section GaussianDomination
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

end GaussianDomination
section GaussianDifferentiation
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
end GaussianDifferentiation
end SK.Analytic
end
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.BoundedDerivatives ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/BoundedDerivatives.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section SmoothRecursion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def BoundedDerivs (f : E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
    (∀ x, ‖fderiv ℝ f x‖ ≤ C) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D)

end SmoothRecursion
end SK.Analytic
end
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.HierarchyJointMoment ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Hierarchy/HierarchyJointMoment.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
def coordinateProjection : (n : ℕ) → Fin n → ParameterSpace n →L[ℝ] ℝ
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (ContinuousLinearMap.snd ℝ (ParameterSpace n) ℝ)
      (fun j => (coordinateProjection n j).comp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)) i
def coordinateLinear (n : ℕ) (a : Fin n → ℝ) : ParameterSpace n →L[ℝ] ℝ :=
  ∑ i, a i • coordinateProjection n i

end SK.Analytic
end
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.FiberGaussian ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/FiberGaussian.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
def fiberGaussian : (n : ℕ) → ℝ → Measure (ParameterSpace n)
  | 0, x => Measure.dirac x
  | n+1, x => (fiberGaussian n x).prod (gaussianReal 0 1)

end SK.Analytic
end
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianGrowth ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/GaussianGrowth.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section GaussianGrowth
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
set_option linter.unusedVariables false in
axiom _root_.SKConstantsOAI.SK.Analytic.HasExpGrowth.mul : ∀ {E : Type} [inst : NormedAddCommGroup E] {f g : E → ℝ},
  SKConstantsOAI.SK.Analytic.HasExpGrowth f →
    SKConstantsOAI.SK.Analytic.HasExpGrowth g →
      SKConstantsOAI.SK.Analytic.HasExpGrowth fun (x : E) ↦ f x * g x

end GaussianGrowth

def coordinateAxis : (n : ℕ) → Fin n → ParameterSpace n
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (0,1) (fun j => (coordinateAxis n j,0)) i

section LinearGrowth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end LinearGrowth
end SK.Analytic
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
end
end
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianResponse ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/GaussianResponse.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
set_option linter.unusedVariables false in
axiom _root_.SKConstantsOAI.SK.Analytic.HasExpGrowth.integrable_tilted_fiberGaussian : ∀ {F : Type} [inst : NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
  (V : SKConstantsOAI.SK.Analytic.ParameterSpace n → ℝ),
  SKConstantsOAI.SK.Analytic.BoundedDerivs V →
    ∀ {g : SKConstantsOAI.SK.Analytic.ParameterSpace n → F},
      SKConstantsOAI.SK.Analytic.HasExpGrowth g →
        Continuous g →
          ∀ (x : ℝ),
            MeasureTheory.Integrable g ((SKConstantsOAI.SK.Analytic.fiberGaussian n x).tilted V)
section Directional
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
end Directional

end SK.Analytic
end
end
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.CoordinateStein ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/CoordinateStein.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
def coordinateVector (n : ℕ) (a : Fin n → ℝ) : ParameterSpace n :=
  ∑ i, a i • coordinateAxis n i
section DirectionalSpinStein
variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
end DirectionalSpinStein
end SK.Analytic
end
end
end
end
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Examples.Example_27803ac30bd2b4c9590e_TiltedDirectionalMoment ====
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Scalar/TiltedDirectionalMoment.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
set_option linter.unusedVariables false in
axiom _root_.SKConstantsOAI.SK.Analytic.HasExpGrowth.pow : ∀ {E : Type} [inst : NormedAddCommGroup E] {f : E → ℝ},
  SKConstantsOAI.SK.Analytic.HasExpGrowth f →
    ∀ (k : ℕ), SKConstantsOAI.SK.Analytic.HasExpGrowth fun (x : E) ↦ f x ^ k


set_option linter.unusedVariables false in
theorem tilted_linear_even_moment_step (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, |fderiv ℝ V z (coordinateVector n a)| ≤ B) (p : ℕ) 
    (h_SKConstantsOAI_SK_Analytic_tilted_linear_moment_recursion : ∀ (n : ℕ) (V : SKConstantsOAI.SK.Analytic.ParameterSpace n → ℝ),
      SKConstantsOAI.SK.Analytic.BoundedDerivs V →
        ∀ (x : ℝ) (a : Fin n → ℝ) (p : ℕ),
          ∫ (z : SKConstantsOAI.SK.Analytic.ParameterSpace n),
              (SKConstantsOAI.SK.Analytic.coordinateLinear n a :
                    SKConstantsOAI.SK.Analytic.ParameterSpace n → ℝ)
                  z ^
                (p + 2) ∂(SKConstantsOAI.SK.Analytic.fiberGaussian n x).tilted V =
            ((↑(p + 1) : ℝ) * ∑ i : Fin n, a i ^ 2) *
                ∫ (z : SKConstantsOAI.SK.Analytic.ParameterSpace n),
                  (SKConstantsOAI.SK.Analytic.coordinateLinear n a :
                        SKConstantsOAI.SK.Analytic.ParameterSpace n → ℝ)
                      z ^
                    p ∂(SKConstantsOAI.SK.Analytic.fiberGaussian n x).tilted V +
              ∫ (z : SKConstantsOAI.SK.Analytic.ParameterSpace n),
                (SKConstantsOAI.SK.Analytic.coordinateLinear n a :
                        SKConstantsOAI.SK.Analytic.ParameterSpace n → ℝ)
                      z ^
                    (p + 1) *
                  (fderiv ℝ V z : SKConstantsOAI.SK.Analytic.ParameterSpace n → ℝ)
                    (SKConstantsOAI.SK.Analytic.coordinateVector n
                      a) ∂(SKConstantsOAI.SK.Analytic.fiberGaussian n x).tilted V)
    (h_SKConstantsOAI_SK_Analytic_HasExpGrowth_of_bounded : ∀ {E F : Type} [inst : Norm E] [inst_1 : Norm F] {f : E → F} {C : ℝ},
      0 ≤ C → (∀ (z : E), ‖f z‖ ≤ C) → SKConstantsOAI.SK.Analytic.HasExpGrowth f)
    (h_SKConstantsOAI_SK_Analytic_HasExpGrowth_linear : ∀ {E : Type} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (L : E →L[ℝ] ℝ),
      SKConstantsOAI.SK.Analytic.HasExpGrowth (⇑L : E → ℝ))
    :
    (∫ z, (coordinateLinear n a z)^(2*p+2) ∂(fiberGaussian n x).tilted V) ≤
      (2*(2*p+1:ℕ)*(∑ i, (a i)^2)+B^2)*
        (∫ z, (coordinateLinear n a z)^(2*p) ∂(fiberGaussian n x).tilted V) := by
  let L := coordinateLinear n a
  let μ := (fiberGaussian n x).tilted V
  let d := fun z => fderiv ℝ V z (coordinateVector n a)
  have hi (k : ℕ) : Integrable (fun z => L z^k) μ :=
    ((h_SKConstantsOAI_SK_Analytic_HasExpGrowth_linear L).pow k).integrable_tilted_fiberGaussian n V hV (L.continuous.pow k) x
  have hd : Continuous d := (hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : HasExpGrowth d := h_SKConstantsOAI_SK_Analytic_HasExpGrowth_of_bounded hB (fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hip : Integrable (fun z => L z^(2*p+1)*d z) μ :=
    (((h_SKConstantsOAI_SK_Analytic_HasExpGrowth_linear L).pow _).mul hdg).integrable_tilted_fiberGaussian n V hV
      ((L.continuous.pow _).mul hd) x
  have hb' (z) : 2*(L z^(2*p+1)*d z) ≤ L z^(2*p+2)+B^2*L z^(2*p) := by
    have hz : 0 ≤ L z^(2*p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    have hdz : d z^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (d z)) hB).mpr (hb z)
    have H := mul_nonneg hz (sq_nonneg (L z-d z))
    have H' := mul_le_mul_of_nonneg_right hdz hz
    simp only [pow_succ] at ⊢
    nlinarith
  have H := integral_mono (hip.const_mul 2) ((hi _).add ((hi _).const_mul (B^2))) hb'
  simp only [Pi.add_apply] at H
  rw [integral_const_mul,integral_add (hi _) ((hi _).const_mul (B^2)),integral_const_mul] at H
  have HE := h_SKConstantsOAI_SK_Analytic_tilted_linear_moment_recursion n V hV x a (2*p)
  change (∫ z, L z^(2*p+2) ∂μ)=(2*p+1:ℕ)*(∑ i, a i^2)*(∫ z, L z^(2*p) ∂μ)+
    ∫ z, L z^(2*p+1)*d z ∂μ at HE
  nlinarith
end SK.Analytic
end
end
end SKConstantsOAI
