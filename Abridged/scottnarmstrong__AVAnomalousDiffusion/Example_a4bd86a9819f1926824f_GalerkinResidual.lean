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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_a4bd86a9819f1926824f_GalerkinResidual ====
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

set_option linter.unusedVariables false in
theorem classicalL2_norm_le_of_all_projection_bounds
    (v : ScalarTorusL2) {B : ℝ}
    (hproj : ∀ N, ‖realFourierProjectionCoefficients N v‖ ≤ B) 
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
    (h_AVenhance_Infra_Parabolic_FourierGalerkin_tendsto_realFourierProjection : ∀ (v : ↥AVenhance.Infra.Parabolic.FourierGalerkin.ScalarTorusL2),
      Filter.Tendsto
        (fun (N : ℕ) ↦
          (AVenhance.Infra.Parabolic.FourierGalerkin.realFourierScalarMap N :
              AVenhance.Infra.Parabolic.FourierGalerkin.Coefficients
                  (AVenhance.Infra.Parabolic.FourierGalerkin.RealFourierDimension N) →
                ↥AVenhance.Infra.Parabolic.FourierGalerkin.ScalarTorusL2)
            (AVenhance.Infra.Parabolic.FourierGalerkin.realFourierProjectionCoefficients N v))
        Filter.atTop (nhds v))
    :
    ‖v‖ ≤ B := by
  have hlim := h_AVenhance_Infra_Parabolic_FourierGalerkin_tendsto_realFourierProjection v
  have hnorm : Tendsto
      (fun N => ‖realFourierScalarMap N (realFourierProjectionCoefficients N v)‖)
      atTop (𝓝 ‖v‖) := by
    exact (continuous_norm.continuousAt.tendsto).comp hlim
  apply le_of_tendsto hnorm
  filter_upwards with N
  simpa only [h_AVenhance_Infra_Parabolic_FourierGalerkin_realFourierScalarMap_norm] using hproj N

end AVenhance.Infra.Classical
end
