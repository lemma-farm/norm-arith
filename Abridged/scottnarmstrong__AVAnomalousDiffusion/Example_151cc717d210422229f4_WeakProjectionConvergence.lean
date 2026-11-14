module

public import Mathlib
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
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
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Bases
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Analysis.Normed.Operator.Basic

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.Homogenization.Ambient.Basic ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.Homogenization.Sobolev.WeakDerivatives ====
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
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume
def HasWeakGradientOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)
namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn
end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.Homogenization.Sobolev.H1.Definitions ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
/-!
`H¹(U)` is modeled here by explicit witnesses: a function, a candidate weak
gradient, `L²` control on both, and the integration-by-parts identity against
smooth compactly supported tests. `H¹₀(U)` adds the usual approximation package
by smooth compactly supported functions supported in `U`.
-/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict U)
def GradMemL2On {d : ℕ} (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.LatticeShift ====
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
/-! Statement file: `latticeShift` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Integer translation `x ↦ x + n` on `Vec 2`. -/
def latticeShift (n : Fin 2 → ℤ) : Vec 2 := fun i => (n i : ℝ)
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.IsZ2Periodic ====
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
/-! Statement file: `IsZ2Periodic` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- ℤ²-periodicity: `f (x + n) = f x` for all `n ∈ ℤ²`, `x ∈ ℝ²`. -/
def IsZ2Periodic {β : Type*} (f : Vec 2 → β) : Prop :=
  ∀ (n : Fin 2 → ℤ) (x : Vec 2), f (x + latticeShift n) = f x
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.UnitCube ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus.Basic ====
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
/-! Basic measurable and periodic infrastructure for the unit torus. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
local instance avInfraTorusBasicMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusBasicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusBasicIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Torus
open Homogenization

/-- The quotient map from Euclidean coordinates to the unit additive torus. -/
def toUnitTorus (d : ℕ) (x : Vec d) : UnitAddTorus (Fin d) :=
  fun i => (x i : UnitAddCircle)
/-- The representative of a torus point in the half-open cell `(0,1]^d`. -/
def unitTorusRepresentative (d : ℕ) (x : UnitAddTorus (Fin d)) : Vec d :=
  fun i => ((AddCircle.equivIoc (1 : ℝ) 0 (x i)).1 : ℝ)
/-- Transfer a Euclidean function to the torus by taking its canonical cell representative. -/
def periodicToTorus {d : ℕ} {α : Type*}
    (f : Vec d → α) : UnitAddTorus (Fin d) → α :=
  fun x => f (unitTorusRepresentative d x)

end AVenhance.Infra.Torus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus.FourierCalculus ====
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
/-! Fourier coefficients of smooth periodic functions and their derivatives. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
open scoped ComplexConjugate
local instance avInfraTorusFourierCalculusMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusFourierCalculusMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusFourierCalculusIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Torus
/-- The Euclidean representative of the torus character with frequency `k`,
using the sign convention in `mFourierCoeff`. -/
def torusCharacter {d : ℕ} (k : Fin d → ℤ) (x : Vec d) : ℂ :=
  UnitAddTorus.mFourier (-k) (toUnitTorus d x)

end AVenhance.Infra.Torus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.IsPeriodicH1With ====
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
/-! Statement file: `IsPeriodicH1With` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Periodic `H¹` with an explicit gradient `Du`. -/
def IsPeriodicH1With (u : Vec 2 → ℝ) (Du : Vec 2 → Vec 2) : Prop :=
  IsZ2Periodic u ∧ IsZ2Periodic Du ∧ MemL2On unitCube u ∧ GradMemL2On unitCube Du ∧
    HasWeakGradientOn Set.univ u Du
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.SpaceGrad ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.TimeCube ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.L2NormSq ====
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
/-! Statement file: `l2NormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- `∫_{(0,1)²} f²`. -/
noncomputable def l2NormSq (f : Vec 2 → ℝ) : ℝ := ∫ x in unitCube, f x ^ 2
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.Basis ====
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
/-!
# Finite symmetric Fourier cutoffs on the two-torus

The frequency box is indexed by integer pairs and is invariant under negation.  The Fourier partial
sum of a real-valued function is therefore real-valued; the real projection below is its real part,
with a theorem identifying its complexification with the partial sum itself.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ComplexConjugate ENNReal
local instance basisMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance basisMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance basisProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
abbrev Torus := UnitAddTorus (Fin 2)
/-- The integer frequency represented by an ordered pair. -/
def pairFrequency (p : ℤ × ℤ) : Fin 2 → ℤ :=
  fun i => if i = 0 then p.1 else p.2

/-- The finite symmetric cutoff `[-N,N]²` in frequency space. -/
def symmetricFrequencyBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.ODE ====
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
/-!
# Finite real Galerkin systems for the weak form

The coordinates below are real coefficients of a finite orthonormal family of periodic modes.
The coefficient matrix records the weak form exactly: the drift entry is the integral of
`(b · D eⱼ) eᵢ`. In particular, no integration by parts is used to move the drift onto the test
mode, and no divergence-free hypothesis occurs.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
local instance galerkinMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance galerkinMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance galerkinProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- Real coefficient vectors with their Euclidean inner product and norm. -/
abbrev Coefficients (n : ℕ) := PiLp 2 (fun _ : Fin n => ℝ)
variable {n : ℕ}

/-- The coefficients of an L² projection onto a finite real orthonormal mode family. -/
def modeProjectionCoefficients (n : ℕ) (mode : Fin n → Torus → ℝ)
    (f : Torus → ℝ) : Coefficients n :=
  WithLp.toLp 2 (fun i => ∫ x, f x * mode i x)

namespace WeakFormGalerkinData
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end WeakFormGalerkinData
end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency ====
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
/-!
# Real sine/cosine modes for symmetric Fourier cutoffs

The integer frequency box is split into the zero frequency and one representative from each pair
`{k, -k}`. Each nonzero representative contributes its real and imaginary character. This module
builds the concrete real-valued modes and their smooth periodic ambient representatives.
-/
@[expose] public section
noncomputable section
open MeasureTheory
local instance realModesMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance realModesMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance realModesProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- The lexicographically positive half of the nonzero integer pairs. -/
def positiveFrequencyPair (p : ℤ × ℤ) : Prop :=
  0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)
/-- One representative from each pair `{p,-p}` in the symmetric frequency box. -/
noncomputable def positiveFrequencyRepresentatives (N : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact (symmetricFrequencyBox N).filter positiveFrequencyPair

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes ====
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
@[expose] public section
noncomputable section
open MeasureTheory
attribute [local instance] realModesMeasureSpace realModesMeasureIsAddHaar realModesProbability
namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The ordered integer frequency of a positive representative. -/
def representativeFrequency {N : ℕ}
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) : Fin 2 → ℤ :=
  pairFrequency p.1

/-- The finite real Fourier index: one constant mode and a cosine/sine pair for each representative.
`Bool.false` selects cosine and `Bool.true` selects sine. -/
abbrev RealFourierIndex (N : ℕ) :=
  Option ({p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N} × Bool)
noncomputable instance realFourierIndexFintype (N : ℕ) : Fintype (RealFourierIndex N) :=
  by
    dsimp [RealFourierIndex]
    infer_instance
/-- Real trigonometric modes on the unit torus, normalized so nonconstant modes have norm one. -/
def realFourierMode (N : ℕ) (a : RealFourierIndex N) (x : Torus) : ℝ :=
  match a with
  | none => 1
  | some (p, isSine) =>
    let z := UnitAddTorus.mFourier (representativeFrequency p) x
    if isSine then Real.sqrt 2 * z.im else Real.sqrt 2 * z.re

/-- The corresponding smooth periodic function on Euclidean representatives. -/
def realFourierModeAmbient (N : ℕ) (a : RealFourierIndex N) (x : Homogenization.Vec 2) : ℝ :=
  match a with
  | none => 1
  | some (p, isSine) =>
    let z := AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p) x
    if isSine then Real.sqrt 2 * z.im else Real.sqrt 2 * z.re

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Projection ====
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
@[expose] public section
noncomputable section
open MeasureTheory
attribute [local instance] realModesMeasureSpace realModesMeasureIsAddHaar realModesProbability
namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The finite real-mode dimension at cutoff `N`. -/
@[irreducible]
def RealFourierDimension (N : ℕ) := Fintype.card (RealFourierIndex N)
/-- Reindex the concrete real Fourier family by the standard finite type used by the ODE layer. -/
noncomputable def realFourierIndexEquivFin (N : ℕ) :
    RealFourierIndex N ≃ Fin (RealFourierDimension N) := by
  unfold RealFourierDimension
  exact Fintype.equivFin _
noncomputable def realFourierModeFin (N : ℕ) :
    Fin (RealFourierDimension N) → Torus → ℝ :=
  fun i => realFourierMode N ((realFourierIndexEquivFin N).symm i)

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarSpace ====
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
/-!
# Scalar spatial `L²` synthesis for the real Fourier frame

The orthonormal scalar Fourier modes synthesize an isometric copy of the finite coefficient
space inside scalar torus `L²`. This is the common state space for the cutoff paths and the
coefficient energy estimate.
-/
@[expose] public section
noncomputable section
open MeasureTheory
local instance scalarSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scalarSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance scalarSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- Scalar-valued spatial `L²` on the unit torus. -/
abbrev ScalarTorusL2 := Lp ℝ 2 (volume : Measure Torus)
set_option linter.unusedVariables false in
axiom _root_.AVenhance.Infra.Parabolic.FourierGalerkin.realFourierModeFin_memLp : ∀ (N : ℕ) (i : Fin (AVenhance.Infra.Parabolic.FourierGalerkin.RealFourierDimension N)),
  MeasureTheory.MemLp (AVenhance.Infra.Parabolic.FourierGalerkin.realFourierModeFin N i) 2
    MeasureTheory.MeasureSpace.volume
/-- The class of one normalized real cutoff mode in scalar `L²`. -/
noncomputable def realFourierModeL2 (N : ℕ) (i : Fin (RealFourierDimension N)) :
    ScalarTorusL2 :=
  (realFourierModeFin_memLp N i).toLp (realFourierModeFin N i)
/-- Synthesis of a finite real coefficient vector as a scalar torus `L²` function. -/
noncomputable def realFourierScalarMap (N : ℕ) :
    Coefficients (RealFourierDimension N) →L[ℝ] ScalarTorusL2 :=
  ∑ i : Fin (RealFourierDimension N),
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (RealFourierDimension N) => ℝ) i).smulRight
      (realFourierModeL2 N i)

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.Density ====
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
/-!
# Density of the real symmetric Fourier cutoffs

The union of the finite real Fourier synthesis ranges is dense in scalar torus `L²`.  This is the
test space used by the weak path compactness argument.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance densityMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance densityMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance densityProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance densityScalarTorusMeasureSeparable : IsSeparable (volume : Measure Torus) :=
  inferInstance
local instance densityTwoNeTopFact : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance densityOneLeTwoFact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
/-- The coefficient vector of the orthogonal cutoff projection of a torus `L²` class. -/
@[irreducible]
def realFourierProjectionCoefficients (N : ℕ) (v : ScalarTorusL2) :
    Coefficients (RealFourierDimension N) :=
  modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) (fun x => v x)

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.IsTestFunction ====
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
/-! Statement file: `IsTestFunction` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Smooth space-periodic test functions on `ℝ × ℝ²`, vanishing for `t ≥ 1`. -/
def IsTestFunction (φ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧
  (∀ t, IsZ2Periodic (φ t)) ∧ ∀ t, 1 ≤ t → ∀ x, φ t x = 0
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.IsWeakSolutionGrad ====
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
/-! Statement file: `IsWeakSolutionGrad` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- The weak-solution notion with the gradient `Dθ` explicit: weak solution on `[0,1] × 𝕋²` of
`∂ₜθ + b·∇θ − κΔθ = 0`, `θ(0) = θ₀`. The drift term is required to be
integrable on the space-time cell, so no integral in the weak form can take the
Bochner junk value. -/
def IsWeakSolutionGrad (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (θ₀ : Vec 2 → ℝ)
    (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ t) ≤ C) ∧
  MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 (volume.restrict timeCube) ∧
  (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2 (volume.restrict timeCube)) ∧
  (∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), IsPeriodicH1With (θ t) (Dθ t)) ∧
  Integrable (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2)) (volume.restrict timeCube) ∧
  (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc (0 : ℝ) 1)) ∧
  (∀ φ : ℝ → Vec 2 → ℝ, IsTestFunction φ →
    ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
        + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
      = ∫ x in unitCube, θ₀ x * φ 0 x)
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.ModePath ====
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
/-!
# Integral paths for weak Fourier coefficients

Testing the weak equation by a spatial Fourier mode and a smooth time factor gives an
ordinary scalar weak equation. The scalar reconstruction lemma then identifies each coefficient
with its absolutely continuous forcing path.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ContDiff
namespace AVenhance.Infra.Parabolic.WeakUniqueness
def weakModePairing (u : ℝ → Vec 2 → ℝ) (ψ : Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, u t x * ψ x
end AVenhance.Infra.Parabolic.WeakUniqueness
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteGalerkinEnergy ====
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
/-!
# Energy identity for finite Fourier coefficients of weak solutions

Each real Fourier coefficient satisfies a scalar integral equation. Applying the finite-path
energy identity coefficientwise and summing gives the exact energy identity for every Fourier
cutoff.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
namespace AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Parabolic.FourierGalerkin
/-- The finite vector of real Fourier coefficients of a weak path at time `t`. -/
def weakFourierCoefficientPath (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    Coefficients (RealFourierDimension N) :=
  WithLp.toLp 2 (fun i => weakModePairing u
    (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t)

end AVenhance.Infra.Parabolic.WeakUniqueness
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjection ====
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
/-!
# Fourier projection of periodic weak gradients

The weak-gradient Fourier multiplier identifies the derivative of each real Fourier
projection with the real Fourier projection of the weak gradient. This gives the slice-wise
`H¹` convergence needed in the weak energy passage.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
namespace AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Parabolic.FourierGalerkin
local instance weakProjectionMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakProjectionMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakProjectionProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakProjectionProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

set_option linter.unusedVariables false in
axiom _root_.AVenhance.Infra.Parabolic.WeakUniqueness.weakProjection_realCellToTorus_memLp : ∀ {f : Homogenization.Vec 2 → ℝ},
  Homogenization.MemL2On AVenhance.unitCube f →
    MeasureTheory.MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2
      MeasureTheory.MeasureSpace.volume
end AVenhance.Infra.Parabolic.WeakUniqueness
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_151cc717d210422229f4_WeakProjectionConvergence ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Strong convergence of weak Fourier cutoffs

The finite real Fourier cutoffs of a weak path converge in spacetime `L²`, together with
their spatial gradients. This is the strong convergence needed to pass the finite coefficient
energy balances to the weak path.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped Topology RealInnerProductSpace
namespace AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Parabolic.FourierGalerkin

local instance weakProjectionConvergenceMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakProjectionConvergenceMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakProjectionConvergenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakProjectionConvergenceProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

noncomputable def weakFourierProjectionL2 (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    ScalarTorusL2 :=
  realFourierScalarMap N (weakFourierCoefficientPath N u t)


set_option linter.unusedVariables false in
/-- The scalar Fourier projection errors converge strongly in time `L²`. The equality with the
cell error is the Pythagorean identity for the finite orthogonal projection. -/
theorem weakFourierProjection_scalarL2_time_integral_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) 
    (h_AVenhance_Infra_Parabolic_FourierGalerkin_realFourierScalarMap_norm : ∀ (N : ℕ)
      (c :
        AVenhance.Infra.Parabolic.FourierGalerkin.Coefficients
          (AVenhance.Infra.Parabolic.FourierGalerkin.RealFourierDimension N)),
      ‖(AVenhance.Infra.Parabolic.FourierGalerkin.realFourierScalarMap N :
              AVenhance.Infra.Parabolic.FourierGalerkin.Coefficients
                  (AVenhance.Infra.Parabolic.FourierGalerkin.RealFourierDimension N) →
                ↥AVenhance.Infra.Parabolic.FourierGalerkin.ScalarTorusL2)
            c‖ =
        ‖c‖)
    (h_AVenhance_Infra_Parabolic_FourierGalerkin_realFourierModeFin_projectionCoefficients_norm_le : ∀ (N : ℕ) {f : AVenhance.Infra.Parabolic.FourierGalerkin.Torus → ℝ}
      (hf : MeasureTheory.MemLp f 2 MeasureTheory.MeasureSpace.volume),
      ‖AVenhance.Infra.Parabolic.FourierGalerkin.modeProjectionCoefficients
            (AVenhance.Infra.Parabolic.FourierGalerkin.RealFourierDimension N)
            (AVenhance.Infra.Parabolic.FourierGalerkin.realFourierModeFin N) f‖ ≤
        ‖MeasureTheory.MemLp.toLp f hf‖)
    (h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakProjection_scalarCoefficient_eq_pairing : ∀ {u : ℝ → Homogenization.Vec 2 → ℝ} {t : ℝ} {N : ℕ},
      AVenhance.Infra.Parabolic.FourierGalerkin.modeProjectionCoefficients
          (AVenhance.Infra.Parabolic.FourierGalerkin.RealFourierDimension N)
          (AVenhance.Infra.Parabolic.FourierGalerkin.realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (u t)) =
        AVenhance.Infra.Parabolic.WeakUniqueness.weakFourierCoefficientPath N u t)
    (h_AVenhance_Infra_Parabolic_WeakUniqueness_weakProjection_scalarTransfer_normSq : ∀ {f : Homogenization.Vec 2 → ℝ} (hf : Homogenization.MemL2On AVenhance.unitCube f),
      ‖MeasureTheory.MemLp.toLp (AVenhance.Infra.Torus.periodicToTorus f)
              (AVenhance.Infra.Parabolic.WeakUniqueness.weakProjection_realCellToTorus_memLp hf)‖ ^
          2 =
        AVenhance.l2NormSq f)
    (h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakFourierProjectionL2_normSq_aestronglyMeasurable : ∀ {b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2} {κ : ℝ} {f : Homogenization.Vec 2 → ℝ}
      {u : ℝ → Homogenization.Vec 2 → ℝ} {Du : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2},
      AVenhance.IsWeakSolutionGrad b κ f u Du →
        ∀ (N : ℕ),
          MeasureTheory.AEStronglyMeasurable
            (fun (t : ℝ) ↦ ‖AVenhance.Infra.Parabolic.WeakUniqueness.weakFourierProjectionL2 N u t‖ ^ 2)
            (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioo 0 1)))
    (h_AVenhance_Infra_Parabolic_WeakUniqueness_weakFourierProjectionL2_normSq_tendsto : ∀ {b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2} {κ : ℝ} {f : Homogenization.Vec 2 → ℝ}
      {u : ℝ → Homogenization.Vec 2 → ℝ} {Du : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2},
      AVenhance.IsWeakSolutionGrad b κ f u Du →
        ∀ t ∈ Set.Icc 0 1,
          Filter.Tendsto
            (fun (N : ℕ) ↦ ‖AVenhance.Infra.Parabolic.WeakUniqueness.weakFourierProjectionL2 N u t‖ ^ 2)
            Filter.atTop (nhds (AVenhance.l2NormSq (u t))))
    (h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakProjection_scalarL2_coefficients_eq_pairing : ∀ {f : Homogenization.Vec 2 → ℝ} (hf : Homogenization.MemL2On AVenhance.unitCube f) (N : ℕ),
      AVenhance.Infra.Parabolic.FourierGalerkin.realFourierProjectionCoefficients N
          (MeasureTheory.MemLp.toLp (AVenhance.Infra.Torus.periodicToTorus f)
            (AVenhance.Infra.Parabolic.WeakUniqueness.weakProjection_realCellToTorus_memLp hf)) =
        AVenhance.Infra.Parabolic.FourierGalerkin.modeProjectionCoefficients
          (AVenhance.Infra.Parabolic.FourierGalerkin.RealFourierDimension N)
          (AVenhance.Infra.Parabolic.FourierGalerkin.realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f))
    (h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakPath_l2NormSq_aestronglyMeasurable : ∀ {b : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2} {κ : ℝ} {f : Homogenization.Vec 2 → ℝ}
      {u : ℝ → Homogenization.Vec 2 → ℝ} {Du : ℝ → Homogenization.Vec 2 → Homogenization.Vec 2},
      AVenhance.IsWeakSolutionGrad b κ f u Du →
        MeasureTheory.AEStronglyMeasurable (fun (t : ℝ) ↦ AVenhance.l2NormSq (u t))
          (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioo 0 1)))
    :
    Tendsto (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2)
      atTop (𝓝 0) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let e : ℕ → ℝ → ℝ := fun N t =>
    AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2
  have heMeas (N : ℕ) : AEStronglyMeasurable (e N) μ := by
    exact (h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakPath_l2NormSq_aestronglyMeasurable hu).sub
      (h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakFourierProjectionL2_normSq_aestronglyMeasurable hu N)
  obtain ⟨C, hC⟩ := hu.2.1
  have hCnonneg : 0 ≤ C := by
    have hzero := hC 0 ⟨le_rfl, by norm_num⟩
    have hmem := (hu.1 0 ⟨le_rfl, by norm_num⟩).2
    rw [← h_AVenhance_Infra_Parabolic_WeakUniqueness_weakProjection_scalarTransfer_normSq hmem] at hzero
    exact le_trans (sq_nonneg ‖(weakProjection_realCellToTorus_memLp hmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u 0))‖) hzero
  have hbound (N : ℕ) : ∀ᵐ t ∂μ, ‖e N t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    let v := (weakProjection_realCellToTorus_memLp (hu.1 t htcc).2).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))
    have hnormv : ‖v‖ ^ 2 = AVenhance.l2NormSq (u t) :=
      h_AVenhance_Infra_Parabolic_WeakUniqueness_weakProjection_scalarTransfer_normSq (hu.1 t htcc).2
    have hprojcoeff : realFourierProjectionCoefficients N v =
        weakFourierCoefficientPath N u t := by
      rw [h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakProjection_scalarL2_coefficients_eq_pairing (hu.1 t htcc).2]
      exact h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakProjection_scalarCoefficient_eq_pairing
    have hcoeffcontract : ‖realFourierProjectionCoefficients N v‖ ≤ ‖v‖ := by
      have hcoeff := h_AVenhance_Infra_Parabolic_FourierGalerkin_realFourierModeFin_projectionCoefficients_norm_le N
        (weakProjection_realCellToTorus_memLp (hu.1 t htcc).2)
      rw [← h_AVenhance_Infra_Parabolic_WeakUniqueness_WeakProjectionConvergence_weakProjection_scalarL2_coefficients_eq_pairing (hu.1 t htcc).2] at hcoeff
      simpa [v] using hcoeff
    have hcontract : ‖weakFourierProjectionL2 N u t‖ ≤ ‖v‖ := by
      rw [weakFourierProjectionL2, ← hprojcoeff, h_AVenhance_Infra_Parabolic_FourierGalerkin_realFourierScalarMap_norm]
      exact hcoeffcontract
    have hprojSq : ‖weakFourierProjectionL2 N u t‖ ^ 2 ≤
        AVenhance.l2NormSq (u t) := by
      rw [← hnormv]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcontract
    have hfull : AVenhance.l2NormSq (u t) ≤ C := hC t htcc
    have hfullNonneg : 0 ≤ AVenhance.l2NormSq (u t) := by
      rw [← hnormv]
      positivity
    have herror : |e N t| ≤ C := by
      change |AVenhance.l2NormSq (u t) -
        ‖weakFourierProjectionL2 N u t‖ ^ 2| ≤ C
      apply abs_le.mpr
      constructor <;> nlinarith
    simpa [Real.norm_eq_abs] using herror
  have hdom : Integrable (fun _ : ℝ => C) μ := by
    have hs : volume (Set.Ioo (0 : ℝ) 1) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Ioo]
      norm_num
    exact integrableOn_const (μ := volume) (s := Set.Ioo (0 : ℝ) 1)
      (C := C) hs (by simp)
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun N => e N t) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hnorm := h_AVenhance_Infra_Parabolic_WeakUniqueness_weakFourierProjectionL2_normSq_tendsto hu t htcc
    have hconst : Tendsto (fun _ : ℕ => AVenhance.l2NormSq (u t)) atTop
        (𝓝 (AVenhance.l2NormSq (u t))) := tendsto_const_nhds
    simpa [e] using hconst.sub hnorm
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => C) heMeas hdom hbound hpoint
  simpa [e, μ] using hDCT
end AVenhance.Infra.Parabolic.WeakUniqueness
end
