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
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.Homogenization.Ambient.Basic ====
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
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.Homogenization.Sobolev.WeakDerivatives ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.UnitCube ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.SpaceGrad ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.TimeCube ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Roots.SpaceTimeGradNormSq ====
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
/-! Statement file: `spaceTimeGradNormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- The squared space-time norm `‖∇θ‖²_{L²((0,1)×𝕋²)}` of a weak gradient `Dθ`. -/
noncomputable def spaceTimeGradNormSq (Dθ : ℝ → Vec 2 → Vec 2) : ℝ :=
  ∫ p in timeCube, vecNormSq (Dθ p.1 p.2)
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Section4.CoarseCoeff.DirectionalCalculus ====
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

/-- Space-time coordinate carrier used only to express the differential operators. -/
abbrev AmnrSpace := ℝ × Vec 2
/-- `none` is the material direction; `some i` is the i-th spatial direction. -/
def amnrDirection (b : AmnrSpace → Vec 2) (d : Option (Fin 2)) (z : AmnrSpace) : AmnrSpace :=
  match d with
  | none => (1, b z)
  | some i => (0, basisVec i)
/-- A directional differential operator on the actual space-time function. -/
def amnrOp (b : AmnrSpace → Vec 2) (d : Option (Fin 2))
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ := fderiv ℝ f z (amnrDirection b d z)
/-- Ordered differential words, with the outermost operator at the head. -/
def amnrWord (b : AmnrSpace → Vec 2) : List (Option (Fin 2)) →
    (AmnrSpace → ℝ) → AmnrSpace → ℝ
  | [], f => f
  | d :: w, f => amnrOp b d (amnrWord b w f)

end AVenhance.Infra.Section4.IterateCalculus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Section4.IteratesWordCommutator ====
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
/-! Exact all-order drift commutators, before quantitative norm estimates. -/
@[expose] public section
noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance
/-- The one-coordinate drift commutator applied to the actual scalar field. -/
def iterateVelocityCommutator (b : AmnrSpace → Vec 2) (i : Fin 2)
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ :=
  fderiv ℝ f z (0, fderiv ℝ b z (0, basisVec i))
/-- Ordered commutator expansion. The outer derivative differentiates all
previous errors, and the new error differentiates the actual velocity once. -/
def iterateWordMaterialError (b : AmnrSpace → Vec 2) :
    List (Fin 2) → (AmnrSpace → ℝ) → AmnrSpace → ℝ
  | [], _ => fun _ => 0
  | i :: w, f => fun z =>
      amnrOp b (some i) (iterateWordMaterialError b w f) z +
      iterateVelocityCommutator b i (amnrWord b (w.map some) f) z

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Section4.IteratesWordDiffusion ====
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
/-! Ordered spatial words and exact diffusion commutation for l.V. -/
@[expose] public section
noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance
/-- Ordered coordinate derivatives, with the outermost derivative first. -/
def iterateSpatialWord : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ
  | [], f => f
  | i :: w, f => fun x => spaceGrad (iterateSpatialWord w f) x i

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Section4.IteratesWordLeibniz ====
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
/-! Exact ordered spatial Leibniz expansions for coefficient-gradient products. -/
@[expose] public section
noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance
/-- Each ordered derivative is assigned to exactly one of the two factors. -/
def iterateSpatialSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | i :: w => (iterateSpatialSplits w).flatMap (fun p => [(i :: p.1, p.2), (p.1, i :: p.2)])

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Section4.IteratesWordSplitPrincipal ====
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
/-! Principal and lower-order terms in the ordered Leibniz expansion. -/
@[expose] public section
noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance
/-- The two derivative orders in every ordered split add to the original order. -/
axiom iterateSpatialSplits_orders (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ iterateSpatialSplits w) :
    p.1.length + p.2.length = w.length

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Section4.IteratesErrorGradientEnergy ====
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
/-! Actual differentiated material-error energy for the previous increment. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual material-error gradient energy requires no differentiated
 error bound as a premise. All natural integrability is proved. -/
axiom iterate_material_error_gradient_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) {B : ℝ}
    (hB : ∀ t x j k, |spaceGrad (fun y => b t y k) x j| ≤ B) :
    spaceTimeGradNormSq (fun t x => spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) (t, y)) x) ≤
      2 * (∑ j : Fin 2, ∫ z in timeCube, iterateWordMaterialError
        (fun z : AmnrSpace => b z.1 z.2) (j :: w) (fun z => v z.1 z.2) z ^ 2) +
      8 * B ^ 2 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (v t)))
end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Infra.Section4.IteratesAnalyticErrorEnergy ====
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
/-! Actual squared material-error energy in analytic weights. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance
/-- Positive analytic velocity jets and actual lower scalar gradient energies
 control the material error square with one squared radius gain. -/
axiom iterate_analytic_material_error_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (a : ℕ)
    {B G r L : ℝ} (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length)) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤ B * (p.1.length.factorial : ℝ) * r ^ p.1.length)
    (hE : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length)),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤
        G ^ 2 * (((p.2.length + a).factorial : ℝ) * L ^ p.2.length) ^ 2) :
    (∫ z in timeCube, iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) z ^ 2) ≤
      32 * B ^ 2 * G ^ 2 * (r / L) ^ 2 * (((w.length + a).factorial : ℝ) * L ^ w.length) ^ 2
end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_fefe352503cc56252361_IteratesAnalyticErrorGradient ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Actual previous material-error gradient in the induction's analytic weights. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance
/-- The actual error-gradient energy uses only scalar gradient orders up to
 n. Its factorial has shift n+a+1, exactly fitting the next increment. -/
theorem iterate_analytic_material_error_gradient_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (a : ℕ)
    {B G r L : ℝ} (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hjet : ∀ t x (q : List (Fin 2)), 1 ≤ q.length → ∀ j,
      |iterateSpatialWord q (fun y => b t y j) x| ≤ B * (q.length.factorial : ℝ) * r ^ q.length)
    (hE : ∀ q : List (Fin 2), q.length ≤ w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (v t))) ≤
        G ^ 2 * (((q.length + a).factorial : ℝ) * L ^ q.length) ^ 2) :
    spaceTimeGradNormSq (fun t x => spaceGrad (fun y => iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) w (fun z => v z.1 z.2) (t, y)) x) ≤
      136 * B ^ 2 * r ^ 2 * G ^ 2 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have hfirst : ∀ t x j k, |spaceGrad (fun y => b t y k) x j| ≤ B * r := by
    intro t x j k
    simpa only [iterateSpatialWord, List.length_cons, List.length_nil, Nat.factorial_one,
      Nat.reduceAdd, Nat.cast_one, mul_one, pow_one] using hjet t x [j] (by simp) k
  have ht := iterate_material_error_gradient_energy_bound hb hv w hfirst
  have he (j : Fin 2) : (∫ z in timeCube, iterateWordMaterialError
      (fun z : AmnrSpace => b z.1 z.2) (j :: w) (fun z => v z.1 z.2) z ^ 2) ≤
      32 * B ^ 2 * r ^ 2 * G ^ 2 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
    have hs := iterate_analytic_material_error_energy_bound hb hv (j :: w) a hL hg
      (B := B) (G := G) (fun t x p hp k => hjet t x p.1
        (by simpa using (List.mem_filter.mp hp).2) k)
      (fun p hp => hE p.2 (by
        have ho := iterateSpatialSplits_orders (j :: w) (List.mem_filter.mp hp).1
        have hl : 1 ≤ p.1.length := by simpa using (List.mem_filter.mp hp).2
        simp only [List.length_cons] at ho
        omega))
    have heq : 32 * B ^ 2 * G ^ 2 * (r / L) ^ 2 *
        (((w.length + 1 + a).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 =
        32 * B ^ 2 * r ^ 2 * G ^ 2 * (((w.length + 1 + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
      simp only [pow_succ]
      field_simp
    simpa only [List.length_cons, heq] using hs
  have hf : ((w.length + a).factorial : ℝ) ≤ ((w.length + 1 + a).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : w.length + a ≤ w.length + 1 + a)
  have hw := (hE w le_rfl).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hf (by positivity : 0 ≤ L ^ w.length)) 2) (sq_nonneg G))
  have hbase := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 8 * (B * r) ^ 2)
  have he0 := he 0
  have he1 := he 1
  simp only [Fin.sum_univ_two] at ht
  nlinarith only [ht, he0, he1, hbase]
end AVenhance.Infra.Section4
