module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Constructions
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.Homogenization.Ambient.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.Homogenization.Sobolev.WeakDerivatives ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

namespace HasWeakPartialDerivOn

end HasWeakPartialDerivOn
end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Roots.UnitCube ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `unitCube` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- The open unit cube `(0,1)²`, a full-measure representative of the fundamental cell of `𝕋²`. -/
def unitCube : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Roots.SpaceGrad ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `spaceGrad` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Classical gradient of a differentiable function, coordinatewise. -/
noncomputable def spaceGrad (f : Vec 2 → ℝ) : Vec 2 → Vec 2 :=
  fun x i => fderiv ℝ f x (basisVec i)
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Roots.TimeCube ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `timeCube` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Space-time cell `(0,1) × (0,1)²`. -/
def timeCube : Set (ℝ × Vec 2) := Set.Ioo (0 : ℝ) 1 ×ˢ unitCube
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Infra.Section4.CoarseCoeff.DirectionalCalculus ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Tensor-independent directional calculus for LeftJacobian iterates.
The operators and proofs are the generic calculus in Amnr/Calculus, isolated
in a namespace so repairs of the Amnr base cannot supply stale proof artifacts.
Their literal formulas agree with the original operators. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4.IterateCalculus
/-! The mixed calculus below keeps spatial and material operations ordered. -/
/-- Scalar material operator. This calculus does not depend on a corrector tensor. -/
def amnrMaterial (b : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  deriv (fun s => f s x) t + vecDot (b t x) (AVenhance.spaceGrad (f t) x)
/-- Space-time coordinate carrier used only to express the differential operators. -/
abbrev AmnrSpace := ℝ × Vec 2

end AVenhance.Infra.Section4.IterateCalculus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Infra.Section4.IteratesTruncatedCell ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Terminal-time cells and monotonicity of actual nonnegative energies. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance
/-- The actual open time cell up to a specified terminal time. -/
def iterateTruncatedCell (s : ℝ) : Set AmnrSpace := Set.Ioo (0 : ℝ) s ×ˢ unitCube

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_3612a2979ebed50e7bf7_IteratesMatrixMaterialPairing ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance
set_option linter.unusedVariables false in
/-- The material contraction pairs linearly with the Hessian contraction on
 every terminal cell, using full nonnegative component energies. -/
theorem iterate_terminal_matrix_material_pairing_bound
    {b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQ : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => Q z.1 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hH : ∀ j k, ContDiffOn ℝ 1 (fun z : AmnrSpace => H z.1 z.2 j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {D G M s : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hQb : ∀ t j k, |Q t j k| ≤ D)
    (hE : ∀ j k, (∫ z in timeCube, (H z.1 z.2 j k) ^ 2) ≤ G ^ 2)
    (hME : ∀ j k, (∫ z in timeCube,
      (amnrMaterial b (fun t x => H t x j k) z.1 z.2) ^ 2) ≤ M ^ 2) 
    (h_AVenhance_Infra_Section4_iterate_integral_pairing_bound : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f g : α → ℝ} {A B : ℝ},
      0 ≤ A →
        0 ≤ B →
          MeasureTheory.Integrable (fun (x : α) ↦ f x ^ 2) μ →
            MeasureTheory.Integrable (fun (x : α) ↦ g x ^ 2) μ →
              MeasureTheory.Integrable (fun (x : α) ↦ f x * g x) μ →
                ∫ (x : α), f x ^ 2 ∂μ ≤ A ^ 2 →
                  ∫ (x : α), g x ^ 2 ∂μ ≤ B ^ 2 → |∫ (x : α), f x * g x ∂μ| ≤ A * B)
    (h_AVenhance_Infra_Section4_iterate_material_matrix_contraction_energy_bound : ∀ {b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
      {H : ℝ → Homogenization.Vec 2 → Matrix (Fin 2) (Fin 2) ℝ},
      ContinuousOn (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ b z.1 z.2)
          (Set.Ici 0 ×ˢ Set.univ) →
        (∀ (j k : Fin 2), ContinuousOn (fun (t : ℝ) ↦ Q t j k) (Set.Ici 0)) →
          (∀ (j k : Fin 2),
              ContDiffOn ℝ 1
                (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ H z.1 z.2 j k)
                (Set.Ici 0 ×ˢ Set.univ)) →
            ∀ {D G : ℝ},
              0 ≤ D →
                (∀ (t : ℝ) (j k : Fin 2), |Q t j k| ≤ D) →
                  (∀ (j k : Fin 2),
                      ∫ (z : ℝ × Homogenization.Vec 2) in AVenhance.timeCube,
                          AVenhance.Infra.Section4.IterateCalculus.amnrMaterial b
                              (fun (t : ℝ) (x : Homogenization.Vec 2) ↦ H t x j k) z.1 z.2 ^
                            2 ≤
                        G ^ 2) →
                    ∫ (z : ℝ × Homogenization.Vec 2) in AVenhance.timeCube,
                        (∑ j : Fin 2,
                            ∑ k : Fin 2,
                              Q z.1 j k *
                                AVenhance.Infra.Section4.IterateCalculus.amnrMaterial b
                                  (fun (t : ℝ) (x : Homogenization.Vec 2) ↦ H t x j k) z.1 z.2) ^
                          2 ≤
                      (4 * D * G) ^ 2)
    (h_AVenhance_Infra_Section4_iterate_material_cross_timeCube_integrable : ∀ {u v : ℝ → Homogenization.Vec 2 → ℝ} {b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2},
      ContinuousOn (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ b z.1 z.2)
          (Set.Ici 0 ×ˢ Set.univ) →
        ContinuousOn (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ u z.1 z.2)
            (Set.Ici 0 ×ˢ Set.univ) →
          ContDiffOn ℝ 1 (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ v z.1 z.2)
              (Set.Ici 0 ×ˢ Set.univ) →
            MeasureTheory.IntegrableOn
              (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦
                u z.1 z.2 * AVenhance.Infra.Section4.IterateCalculus.amnrMaterial b v z.1 z.2)
              AVenhance.timeCube MeasureTheory.MeasureSpace.volume)
    (h_AVenhance_Infra_Section4_iterate_material_matrix_contraction_square_integrable : ∀ {b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
      {H : ℝ → Homogenization.Vec 2 → Matrix (Fin 2) (Fin 2) ℝ},
      ContinuousOn (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ b z.1 z.2)
          (Set.Ici 0 ×ˢ Set.univ) →
        (∀ (j k : Fin 2), ContinuousOn (fun (t : ℝ) ↦ Q t j k) (Set.Ici 0)) →
          (∀ (j k : Fin 2),
              ContDiffOn ℝ 1
                (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ H z.1 z.2 j k)
                (Set.Ici 0 ×ˢ Set.univ)) →
            MeasureTheory.IntegrableOn
              (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦
                (∑ j : Fin 2,
                    ∑ k : Fin 2,
                      Q z.1 j k *
                        AVenhance.Infra.Section4.IterateCalculus.amnrMaterial b
                          (fun (t : ℝ) (x : Homogenization.Vec 2) ↦ H t x j k) z.1 z.2) ^
                  2)
              AVenhance.timeCube MeasureTheory.MeasureSpace.volume)
    (h_AVenhance_Infra_Section4_iterate_truncated_integral_eq_interval_of_integrable : ∀ {f : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace → ℝ},
      MeasureTheory.IntegrableOn f AVenhance.timeCube MeasureTheory.MeasureSpace.volume →
        ∀ {s : ℝ},
          0 ≤ s →
            s ≤ 1 →
              ∫ (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) in
                  AVenhance.Infra.Section4.iterateTruncatedCell s, f z =
                ∫ (t : ℝ) in 0..s, ∫ (x : Homogenization.Vec 2) in AVenhance.unitCube, f (t, x))
    (h_AVenhance_Infra_Section4_iterate_matrix_contraction_spacetime_energy_bound : ∀ {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {H : ℝ → Homogenization.Vec 2 → Matrix (Fin 2) (Fin 2) ℝ},
      (∀ (j k : Fin 2),
          ContinuousOn (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ Q z.1 j k)
            (Set.Ici 0 ×ˢ Set.univ)) →
        (∀ (j k : Fin 2),
            ContinuousOn (fun (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) ↦ H z.1 z.2 j k)
              (Set.Ici 0 ×ˢ Set.univ)) →
          ∀ {D G : ℝ},
            0 ≤ D →
              (∀ (t : ℝ) (j k : Fin 2), |Q t j k| ≤ D) →
                (∀ (j k : Fin 2),
                    ∫ (z : ℝ × Homogenization.Vec 2) in AVenhance.timeCube, H z.1 z.2 j k ^ 2 ≤ G ^ 2) →
                  ∫ (z : ℝ × Homogenization.Vec 2) in AVenhance.timeCube,
                      (∑ j : Fin 2, ∑ k : Fin 2, Q z.1 j k * H z.1 z.2 j k) ^ 2 ≤
                    (4 * D * G) ^ 2)
    (h_AVenhance_Infra_Section4_iterateTruncatedCell_subset : ∀ {s : ℝ}, s ≤ 1 → AVenhance.Infra.Section4.iterateTruncatedCell s ⊆ AVenhance.timeCube)
    (h_AVenhance_Infra_Section4_iterate_truncated_nonnegative_integral_le : ∀ {f : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace → ℝ},
      MeasureTheory.IntegrableOn f AVenhance.timeCube MeasureTheory.MeasureSpace.volume →
        (∀ (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace), 0 ≤ f z) →
          ∀ {s : ℝ},
            s ≤ 1 →
              ∫ (z : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace) in
                  AVenhance.Infra.Section4.iterateTruncatedCell s, f z ≤
                ∫ (z : ℝ × Homogenization.Vec 2) in AVenhance.timeCube, f z)
    (h_AVenhance_Infra_Section4_iterate_timeCube_integrable_of_continuousOn : ∀ {f : AVenhance.Infra.Section4.IterateCalculus.AmnrSpace → ℝ},
      ContinuousOn f (Set.Ici 0 ×ˢ Set.univ) →
        MeasureTheory.IntegrableOn f AVenhance.timeCube MeasureTheory.MeasureSpace.volume)
    :
    |∫ t in 0..s, ∫ x in unitCube,
      (∑ j : Fin 2, ∑ k : Fin 2, Q t j k *
        amnrMaterial b (fun r y => H r y j k) t x) *
      (∑ j : Fin 2, ∑ k : Fin 2, Q t j k * H t x j k)| ≤ 16 * D ^ 2 * M * G := by
  let f := fun t x => ∑ j : Fin 2, ∑ k : Fin 2, Q t j k * H t x j k
  let a := fun t x => ∑ j : Fin 2, ∑ k : Fin 2,
    Q t j k * amnrMaterial b (fun r y => H r y j k) t x
  have hf : ContinuousOn (fun z : AmnrSpace => f z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun k _ => (hQ j k).mul (hH j k)))).continuousOn
  have hQc (j k : Fin 2) : ContinuousOn (fun t => Q t j k) (Set.Ici (0 : ℝ)) :=
    (hQ j k).continuousOn.comp (continuousOn_id.prodMk (continuousOn_const (c := (0 : Vec 2))))
      (fun _ ht => ⟨ht, Set.mem_univ _⟩)
  have haI := h_AVenhance_Infra_Section4_iterate_material_matrix_contraction_square_integrable hb hQc hH
  have hfI := h_AVenhance_Infra_Section4_iterate_timeCube_integrable_of_continuousOn (hf.pow 2)
  have hpI : IntegrableOn (fun z : AmnrSpace => a z.1 z.2 * f z.1 z.2) timeCube := by
    have hi (j k : Fin 2) := h_AVenhance_Infra_Section4_iterate_material_cross_timeCube_integrable
      (u := fun t x => f t x * Q t j k) (v := fun t x => H t x j k)
      hb (hf.mul (hQ j k).continuousOn) (hH j k)
    have ht := integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi j k))
    unfold IntegrableOn
    convert ht using 1
    funext z
    dsimp only [a]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have haE := h_AVenhance_Infra_Section4_iterate_material_matrix_contraction_energy_bound hb hQc hH hD hQb hME
  have hfE := h_AVenhance_Infra_Section4_iterate_matrix_contraction_spacetime_energy_bound
    (fun j k => (hQ j k).continuousOn) (fun j k => (hH j k).continuousOn) hD hQb hE
  have hsub := h_AVenhance_Infra_Section4_iterateTruncatedCell_subset hs1
  have ht := h_AVenhance_Infra_Section4_iterate_integral_pairing_bound
    (by positivity : 0 ≤ 4 * D * M) (by positivity : 0 ≤ 4 * D * G)
    (haI.mono_set hsub) (hfI.mono_set hsub) (hpI.mono_set hsub)
    ((h_AVenhance_Infra_Section4_iterate_truncated_nonnegative_integral_le haI (fun _ => sq_nonneg _) hs1).trans haE)
    ((h_AVenhance_Infra_Section4_iterate_truncated_nonnegative_integral_le hfI (fun _ => sq_nonneg _) hs1).trans hfE)
  rw [h_AVenhance_Infra_Section4_iterate_truncated_integral_eq_interval_of_integrable hpI hs hs1] at ht
  exact ht.trans_eq (by ring)
end AVenhance.Infra.Section4
