module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
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
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.Basis ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.ODE ====
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

/-- The function represented by a finite real coefficient vector. -/
def modeExpansion (n : ℕ) (mode : Fin n → Torus → ℝ)
    (c : Coefficients n) (x : Torus) : ℝ :=
  ∑ i, c i * mode i x

namespace WeakFormGalerkinData
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end WeakFormGalerkinData
end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.Homogenization.Ambient.Basic ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.Homogenization.Sobolev.WeakDerivatives ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Torus.FourierCalculus ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Statements.Roots.SpaceGrad ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes ====
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

/-- The Euclidean gradient field attached to a real Fourier mode. -/
def realFourierModeAmbientGrad (N : ℕ) (a : RealFourierIndex N)
    (x : Homogenization.Vec 2) : Homogenization.Vec 2 :=
  AVenhance.spaceGrad (realFourierModeAmbient N a) x

/-- The periodic gradient mode on the quotient torus. -/
def realFourierModeGrad (N : ℕ) (a : RealFourierIndex N) (x : Torus) :
    Homogenization.Vec 2 :=
  AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientGrad N a) x

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Projection ====
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

/-- The scalar Fourier mode family with `Fin` indices. -/
noncomputable def realFourierModeFin (N : ℕ) :
    Fin (RealFourierDimension N) → Torus → ℝ :=
  fun i => realFourierMode N ((realFourierIndexEquivFin N).symm i)
/-- The gradient family with the matching `Fin` indices. -/
noncomputable def realFourierModeGradFin (N : ℕ) :
    Fin (RealFourierDimension N) → Torus → Homogenization.Vec 2 :=
  fun i => realFourierModeGrad N ((realFourierIndexEquivFin N).symm i)

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.GradientSpace ====
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
# The spatial `L²` gradient space for real Fourier cutoffs

This module places the explicitly differentiated real modes in the vector-valued torus `L²`
space and packages their finite synthesis as a continuous linear map. The Euclidean norm on the
two gradient coordinates is the `PiLp 2` norm, matching the gradient energy.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
local instance gradientSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance gradientSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance gradientSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- Euclidean two-vectors with their usual squared-sum norm. -/
abbrev SpatialVector := PiLp 2 (fun _ : Fin 2 => ℝ)
/-- The Hilbert space of square-integrable spatial vector fields on the unit torus. -/
abbrev SpatialGradientL2 := Lp SpatialVector 2 (volume : Measure Torus)

/-- Every real Fourier gradient mode is an element of vector-valued spatial `L²`. -/
axiom realFourierModeGradFin_memLp (N : ℕ) (i : Fin (RealFourierDimension N)) :
    MemLp (fun x : Torus =>
      (WithLp.toLp 2 (realFourierModeGradFin N i x) : SpatialVector))
      2 (volume : Measure Torus)
/-- A real Fourier gradient mode, represented as an `L²` equivalence class. -/
noncomputable def realFourierModeGradL2 (N : ℕ)
    (i : Fin (RealFourierDimension N)) : SpatialGradientL2 :=
  (realFourierModeGradFin_memLp N i).toLp
    (fun x : Torus => WithLp.toLp 2 (realFourierModeGradFin N i x))
/-- Finite synthesis of the vector-valued gradient modes. -/
noncomputable def realFourierGradientMap (N : ℕ) :
    Coefficients (RealFourierDimension N) →L[ℝ] SpatialGradientL2 :=
  ∑ i : Fin (RealFourierDimension N),
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (RealFourierDimension N) => ℝ) i).smulRight
      (realFourierModeGradL2 N i)
@[simp]
axiom realFourierGradientMap_apply (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    realFourierGradientMap N c =
      ∑ i : Fin (RealFourierDimension N), (c i) • realFourierModeGradL2 N i
end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDrift ====
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
# Drift estimates from the boundedness hypothesis

The weak-wellposedness root assumes a pointwise bound on the ambient drift. Since `Vec 2`
uses the product sup norm while the spatial gradient energy is Euclidean, the dimension-two bridge
below records the harmless factor `sqrt 2`. No divergence-free assumption is used.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The Euclidean norm associated with the squared vector norm used by the carriers. -/
def euclideanVecNorm (v : Vec 2) : ℝ := Real.sqrt (Homogenization.vecNormSq v)
axiom euclideanVecNorm_nonneg (v : Vec 2) : 0 ≤ euclideanVecNorm v

/-- The pointwise bound controls the Euclidean dot product, with the conversion from the
product sup norm to the Euclidean norm made explicit. -/
axiom vecDot_le_of_supNorm_le {b v : Vec 2} {C : ℝ}
    (hC : 0 ≤ C) (hb : ‖b‖ ≤ C) :
    |Homogenization.vecDot b v| ≤ (Real.sqrt 2 * C) * euclideanVecNorm v

/-- The same `L²` drift estimate holds without a measurability premise on the integrand: if the
Bochner integral is undefined, Mathlib's integral convention assigns it zero. This form is useful
for pointwise matrix bounds when the product-measurability hypothesis controls slices only
for almost every time. -/
axiom driftIntegral_bound_of_L2_or_not {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g u : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hpoint : ∀ᵐ x ∂μ, |f x| ≤ B * (|g x| * |u x|))
    (hg : MemLp g 2 μ) (hu : MemLp u 2 μ) :
    |∫ x, f x ∂μ| ≤
      B * (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, ‖u x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8d171bc58797.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData ====
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

/-- The finite pointwise real Fourier gradient sum belongs to scalar `L²` after taking its
Euclidean norm. -/
axiom realFourierGradientExpansion_norm_memLp (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    MemLp (fun x : Torus => euclideanVecNorm
      (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x)) 2 volume
/-- The finite pointwise real Fourier scalar sum belongs to scalar `L²`. -/
axiom realFourierScalarExpansion_memLp (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    MemLp (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c) 2 volume
/-- The gradient factor of the finite Fourier sum is its vector `L²` norm. -/
axiom realFourierGradientExpansion_l2Factor (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    (∫ x : Torus, euclideanVecNorm
      (∑ i : Fin (RealFourierDimension N), c i • realFourierModeGradFin N i x) ^
        (2 : ℝ)) ^ ((1 : ℝ) / 2) = ‖realFourierGradientMap N c‖
/-- The scalar factor of the finite Fourier sum is the coefficient norm. -/
axiom realFourierScalarExpansion_l2Factor (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    (∫ x : Torus,
      ‖modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x‖ ^ (2 : ℝ)) ^
        ((1 : ℝ) / 2) = ‖c‖
/-- The square-integral factor of a normalized scalar Fourier mode. -/
def realFourierModeFin_l2Factor (N : ℕ) (i : Fin (RealFourierDimension N)) : ℝ :=
  (∫ x : Torus, ‖realFourierModeFin N i x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)

/-- The quadratic drift form obtained by expanding a positive-cutoff real Fourier sum. -/
@[irreducible]
noncomputable def positiveCutoffGradientMap (N : ℕ) :
    Coefficients (RealFourierDimension N) →L[ℝ] SpatialGradientL2 :=
  realFourierGradientMap N

/-- The explicit dot-product constant associated with the drift bound. -/
noncomputable def positiveCutoffDriftConstant (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) : ℝ :=
  Real.sqrt 2 * Classical.choose hb_bdd

end AVenhance.Infra.Parabolic.FourierGalerkin
end

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_a1c9ae21d6e34d34914e_BilinearForms ====
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
# Mixed Fourier weak forms

The finite ODE is tested by a potentially different Fourier vector from its evolving trial
vector.  These identities retain that bilinear structure and give bounds with constants that do
not depend on the cutoff.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
open scoped RealInnerProductSpace
local instance bilinearFormsMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance bilinearFormsMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance bilinearFormsProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Parabolic.FourierGalerkin
/-- Spatial drift form with independent trial and test Fourier coefficients. -/
def realFourierDriftBilinearForm (N : ℕ) (drift : ℝ → Torus → Vec 2) (t : ℝ)
    (c d : Coefficients (RealFourierDimension N)) : ℝ :=
  ∫ x : Torus,
    Homogenization.vecDot (drift t x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x


/-- Mixed drift estimate, uniform in the real Fourier cutoff. -/
theorem positiveCutoffDriftBilinear_bound (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2)
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (c d : Coefficients (RealFourierDimension N)) :
    |realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c d| ≤
      positiveCutoffDriftConstant b hb_bdd *
        ‖positiveCutoffGradientMap N c‖ * ‖d‖ := by
  let C : ℝ := Classical.choose hb_bdd
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C :=
    Classical.choose_spec hb_bdd
  have hC_nonneg : 0 ≤ C := by
    have h := hC (1 / 2) (by norm_num) 0
    exact (norm_nonneg _).trans h
  let B : ℝ := Real.sqrt 2 * C
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) hC_nonneg
  have hdot : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x v,
      |Homogenization.vecDot (b t x) v| ≤ B * euclideanVecNorm v := by
    intro s hs x v
    exact vecDot_le_of_supNorm_le hC_nonneg (hC s hs x)
  let f : Torus → ℝ := fun x =>
    Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x
  let g : Torus → ℝ := fun x => euclideanVecNorm
    (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)
  let u : Torus → ℝ := modeExpansion (RealFourierDimension N) (realFourierModeFin N) d
  have hpoint : ∀ᵐ x ∂(volume : Measure Torus), |f x| ≤ B * (|g x| * |u x|) := by
    filter_upwards with x
    have hb := hdot t ht (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
      (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)
    have hrep : AVenhance.Infra.Torus.periodicToTorus (b t) x =
        b t (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) := rfl
    change |Homogenization.vecDot (AVenhance.Infra.Torus.periodicToTorus (b t) x)
        (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x) *
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x| ≤ _
    rw [hrep]
    calc
      _ = |Homogenization.vecDot (b t
          (AVenhance.Infra.Torus.unitTorusRepresentative 2 x))
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)| *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x| := abs_mul _ _
      _ ≤ (B * euclideanVecNorm
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)) *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x| :=
        mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = B * (|euclideanVecNorm
          (∑ j : Fin (RealFourierDimension N), c j • realFourierModeGradFin N j x)| *
          |modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x|) := by
        rw [abs_of_nonneg (euclideanVecNorm_nonneg _)]
        ring
  have hbound := driftIntegral_bound_of_L2_or_not f g u B hB hpoint
    (realFourierGradientExpansion_norm_memLp N c) (realFourierScalarExpansion_memLp N d)
  have hgradFactor : (∫ x : Torus, ‖g x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) =
      ‖positiveCutoffGradientMap N c‖ := by
    simpa [g, positiveCutoffGradientMap] using realFourierGradientExpansion_l2Factor N c
  have hscalarFactor : (∫ x : Torus, ‖u x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = ‖d‖ := by
    simpa [u, Real.norm_eq_abs] using realFourierScalarExpansion_l2Factor N d
  have hform : realFourierDriftBilinearForm N
      (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c d = ∫ x, f x := rfl
  rw [hgradFactor, hscalarFactor] at hbound
  calc
    |realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (b s)) t c d| =
        |∫ x, f x| := congrArg abs hform
    _ ≤ B * ‖positiveCutoffGradientMap N c‖ * ‖d‖ := by
      simpa [hgradFactor, hscalarFactor] using hbound
    _ = positiveCutoffDriftConstant b hb_bdd *
        ‖positiveCutoffGradientMap N c‖ * ‖d‖ := by
      rfl
end AVenhance.Infra.Parabolic.FourierGalerkin
end
