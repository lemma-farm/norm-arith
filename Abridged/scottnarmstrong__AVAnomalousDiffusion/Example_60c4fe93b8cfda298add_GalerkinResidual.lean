module

public import Mathlib
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Module.Basic
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
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Data.List.OfFn
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.Homogenization.Ambient.Basic ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.Homogenization.Sobolev.WeakDerivatives ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Roots.LatticeShift ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Roots.IsZ2Periodic ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Roots.UnitCube ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Roots.SpaceGrad ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Roots.GradNormSq ====
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
/-! Statement file: `gradNormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- `∫_{(0,1)²} |Du|²` (Euclidean length of the gradient). -/
noncomputable def gradNormSq (Du : Vec 2 → Vec 2) : ℝ := ∫ x in unitCube, vecNormSq (Du x)
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.Basic ====
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
/-- A translated half-open fundamental cell `(aᵢ,aᵢ+1]^d`. -/
def unitCellAt (d : ℕ) (a : Fin d → ℝ) : Set (Vec d) :=
  {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)}
/-- The half-open fundamental cell `(0,1]^d`. This convention matches
`UnitAddTorus.measurableEquivPiIoc` and gives an exact fundamental domain. -/
def unitCell (d : ℕ) : Set (Vec d) := unitCellAt d (fun _ => 0)

axiom measurableSet_unitCell (d : ℕ) : MeasurableSet (unitCell d)

/-- Set integrals over the generic half-open cell and the open square agree. -/
axiom integral_unitCell_eq_unitCube {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec 2 → E) :
    ∫ x in unitCell 2, f x = ∫ x in AVenhance.unitCube, f x

/-- The representative of a torus point in the half-open cell `(0,1]^d`. -/
def unitTorusRepresentative (d : ℕ) (x : UnitAddTorus (Fin d)) : Vec d :=
  fun i => ((AddCircle.equivIoc (1 : ℝ) 0 (x i)).1 : ℝ)
/-- Transfer a Euclidean function to the torus by taking its canonical cell representative. -/
def periodicToTorus {d : ℕ} {α : Type*}
    (f : Vec d → α) : UnitAddTorus (Fin d) → α :=
  fun x => f (unitTorusRepresentative d x)

/-- Integration on the torus agrees with integration of the periodic transfer on the unit cell. -/
axiom integral_periodicToTorus_eq_unitCell {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E) :
    ∫ x : UnitAddTorus (Fin d), periodicToTorus f x = ∫ x in unitCell d, f x
end AVenhance.Infra.Torus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.Homogenization.Ambient.HilbertFinite ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
/-!
This file provides finite-dimensional Hilbert realizations of `\R^d` and
`\R^{2d}` that stay compatible with the project's anti-`EuclideanSpace`
architecture.

The ambient algebraic carriers remain

- `Vec d = Fin d → ℝ`,
- `BlockVec d = Vec d × Vec d`.

Those are excellent lightweight types for most of the development, but their
default normed-space instances are not the Euclidean `L²` ones needed for the
Hilbert-space part of the coarse-graining theory. For that role we introduce
separate wrappers built from `PiLp 2`.
-/
/-- The Euclidean Hilbert realization of `\R^d`, presented without exposing
`EuclideanSpace` in the public API. -/
abbrev HilbertVec (d : ℕ) := PiLp 2 (fun _ : Fin d => ℝ)
namespace HilbertVec

@[ext] axiom ext {d : ℕ} {x y : HilbertVec d} (h : ∀ i, x i = y i) : x = y

end HilbertVec

namespace HilbertMat

end HilbertMat

namespace HilbertBlockVec

end HilbertBlockVec
end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.Calculus ====
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
/-! Smooth periodic integration by parts on half-open fundamental cells. -/
@[expose] public section
noncomputable section
open MeasureTheory Set intervalIntegral
open Homogenization
namespace AVenhance.Infra.Torus
/-- The classical coordinate derivative, evaluated in the unit coordinate direction. -/
noncomputable def coordDeriv {d : ℕ} (i : Fin d) (f : Vec d → ℂ) (x : Vec d) : ℂ :=
  fderiv ℝ f x (basisVec i)
end AVenhance.Infra.Torus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.FourierCalculus ====
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

axiom integral_unitCell_gradSq_eq_sum_coord {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) :
    (∑ i : Fin (n + 1), ∫ x in unitCell (n + 1), ‖coordDeriv i f x‖ ^ 2) =
      ∫ x in unitCell (n + 1),
        ∑ i : Fin (n + 1), ‖coordDeriv i f x‖ ^ 2
end AVenhance.Infra.Torus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.FrozenBridge ====
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
/-! Real-valued d = 2 corollaries in the paper carriers. -/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
namespace AVenhance.Infra.Torus
/-- Regard a real-valued Euclidean function as complex-valued. -/
def realToComplex (f : Vec 2 → ℝ) : Vec 2 → ℂ := Complex.ofRealCLM ∘ f
/-- The complex coordinate derivative of the real cast is the cast of the
classical gradient. -/
axiom coordDeriv_realToComplex {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (x : Vec 2) :
    coordDeriv i (realToComplex f) x = (AVenhance.spaceGrad f x i : ℂ)
end AVenhance.Infra.Torus

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.PeriodicCalculus ====
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
/-! Real-valued periodic integration by parts on the unit cell. -/
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open Set
open AVenhance.Infra.Torus
namespace AVenhance.Infra.Classical
axiom periodic_spaceGrad_component {f : Vec 2 → ℝ}
    (hper : AVenhance.IsZ2Periodic f) (i : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad f x i)
end AVenhance.Infra.Classical
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.Basis ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.ODE ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes ====
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

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Projection ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarSpace ====
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

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData ====
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
# Positive real Fourier Galerkin data for the drift

This module instantiates the abstract finite weak-form ODE by the positive symmetric real Fourier
cutoff. The coefficient datum is the quotient-torus representative of the initial datum.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
open scoped ENNReal RealInnerProductSpace
local instance concreteDataMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance concreteDataMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance concreteDataProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The scalar `L²` norm squared is the integral of the pointwise squared norm. -/
axiom l2_norm_sq_eq_integral_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : Lp E 2 (volume : Measure Torus)) :
    ‖f‖ ^ 2 = ∫ x : Torus, ‖f x‖ ^ 2
end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.GalerkinGenerator ====
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
/-! Finite Fourier generator identities used in the classical Galerkin estimates. -/
@[expose] public section
noncomputable section
open MeasureTheory
local instance classicalGeneratorMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalGeneratorMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalGeneratorProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.FourierGalerkin
open Homogenization

/-- The torus representative of a continuous periodic scalar is square-integrable. -/
axiom memLp_periodicToTorus_real {f : Vec 2 → ℝ}
    (hf : Continuous f) (hper : AVenhance.IsZ2Periodic f) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2
      (volume : Measure Torus)
end AVenhance.Infra.Classical
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.Density ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_60c4fe93b8cfda298add_GalerkinResidual ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Cutoff tails of smooth real periodic residuals. -/
@[expose] public section
noncomputable section
open MeasureTheory
open Filter
open scoped Topology
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
local instance classicalResidualMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalResidualMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalResidualProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Classical
axiom GalerkinResidual.continuous_spaceGrad_component {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i)
axiom classicalL2_norm_le_of_all_projection_bounds
    (v : ScalarTorusL2) {B : ℝ}
    (hproj : ∀ N, ‖realFourierProjectionCoefficients N v‖ ≤ B) :
    ‖v‖ ≤ B
/-- Uniform bounds for all scalar Fourier projections of each derivative component bound the
full Dirichlet energy of a smooth periodic function. -/
theorem classicalSmoothSource_gradient_energy_le_of_projection_bounds
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ 1 f)
    (hper : AVenhance.IsZ2Periodic f) {B : ℝ} (hB : 0 ≤ B)
    (hproj : ∀ i K,
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad f x i))‖ ≤ B) :
    AVenhance.gradNormSq (AVenhance.spaceGrad f) ≤ 2 * B ^ 2 := by
  let g (i : Fin 2) : Vec 2 → ℝ := fun x => AVenhance.spaceGrad f x i
  let v (i : Fin 2) : ScalarTorusL2 :=
    (memLp_periodicToTorus_real (GalerkinResidual.continuous_spaceGrad_component hf i)
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).toLp
      (AVenhance.Infra.Torus.periodicToTorus (g i))
  have hvproj (i : Fin 2) (K : ℕ) :
      realFourierProjectionCoefficients K (v i) =
        modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus (g i)) := by
    unfold realFourierProjectionCoefficients
    ext m
    simp only [modeProjectionCoefficients, PiLp.toLp_apply]
    apply integral_congr_ae
    filter_upwards [(memLp_periodicToTorus_real
      (GalerkinResidual.continuous_spaceGrad_component hf i)
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).coeFn_toLp] with x hx
    rw [hx]
  have hvbound (i : Fin 2) : ‖v i‖ ≤ B := by
    apply classicalL2_norm_le_of_all_projection_bounds
    intro K
    rw [hvproj]
    simpa [g] using hproj i K
  have hcomponent (i : Fin 2) :
      ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 ≤ B ^ 2 := by
    have hnorm := AVenhance.Infra.Parabolic.FourierGalerkin.l2_norm_sq_eq_integral_sq (v i)
    have hcell : (∫ x : Torus, ‖v i x‖ ^ 2) =
        ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 := by
      calc
        (∫ x : Torus, ‖v i x‖ ^ 2) =
            ∫ x : Torus,
              ‖AVenhance.Infra.Torus.periodicToTorus (g i) x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [(memLp_periodicToTorus_real
            (GalerkinResidual.continuous_spaceGrad_component hf i)
            (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).coeFn_toLp]
            with x hx
          rw [show (v i) x =
            ((memLp_periodicToTorus_real
              (GalerkinResidual.continuous_spaceGrad_component hf i)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).toLp
              (AVenhance.Infra.Torus.periodicToTorus (g i))) x by rfl, hx]
        _ = ∫ x : Torus,
            AVenhance.Infra.Torus.periodicToTorus (fun y : Vec 2 => (g i y) ^ 2) x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [AVenhance.Infra.Torus.periodicToTorus]
        _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, (g i x) ^ 2 :=
          AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell _
        _ = ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 := by
          rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
    calc
      ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 = ‖v i‖ ^ 2 := by
        rw [← hcell, ← hnorm]
      _ ≤ B ^ 2 := by nlinarith [hvbound i, norm_nonneg (v i), hB]
  have hgradIdent :
      (∑ i : Fin 2, ∫ x in AVenhance.unitCube,
        (AVenhance.spaceGrad f x i) ^ 2) =
        AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
    let fc : Vec 2 → ℂ := AVenhance.Infra.Torus.realToComplex f
    have hfc : ContDiff ℝ 1 fc := Complex.ofRealCLM.contDiff.comp hf
    have hsum := AVenhance.Infra.Torus.integral_unitCell_gradSq_eq_sum_coord hfc
    have hcoord (i : Fin 2) (x : Vec 2) :
        AVenhance.Infra.Torus.coordDeriv i fc x =
          (AVenhance.spaceGrad f x i : ℂ) :=
      AVenhance.Infra.Torus.coordDeriv_realToComplex hf i x
    calc
      (∑ i : Fin 2, ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x i) ^ 2) =
          ∑ i : Fin 2, ∫ x in AVenhance.Infra.Torus.unitCell 2,
            ‖AVenhance.Infra.Torus.coordDeriv i fc x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
        apply setIntegral_congr_ae
          (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        filter_upwards with x _hx
        rw [hcoord]
        simp
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          ∑ i : Fin 2, ‖AVenhance.Infra.Torus.coordDeriv i fc x‖ ^ 2 := hsum
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          Homogenization.vecNormSq (AVenhance.spaceGrad f x) := by
        apply setIntegral_congr_ae
          (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        filter_upwards with x _hx
        simp [Homogenization.vecNormSq, Homogenization.vecDot, hcoord, pow_two]
      _ = ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq (AVenhance.spaceGrad f x) :=
        AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _
      _ = AVenhance.gradNormSq (AVenhance.spaceGrad f) := rfl
  calc
    AVenhance.gradNormSq (AVenhance.spaceGrad f) =
        ∑ i : Fin 2, ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x i) ^ 2 := hgradIdent.symm
    _ ≤ ∑ _i : Fin 2, B ^ 2 := Finset.sum_le_sum fun i hi => hcomponent i
    _ = 2 * B ^ 2 := by norm_num
end AVenhance.Infra.Classical
end
