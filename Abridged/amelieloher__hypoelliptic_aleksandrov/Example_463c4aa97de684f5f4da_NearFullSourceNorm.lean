module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Set.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.PDEFoundation.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/
@[expose] public section
namespace PDE
/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ
/-- Real `d × d` matrices acting on project vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.HypoellipticAleksandrov.Geometry.KineticPoint ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Kinetic spacetime points

This module gives an explicit carrier for kinetic spacetime. Its fields make
the time, position, and velocity coordinate order visible in every theorem
surface.

## Main definitions

* `KineticPoint d` is a kinetic spacetime point with time, position, and
  velocity coordinates.
* `KineticPoint.homeomorphProd d` identifies this explicit carrier with
  `ℝ × (PDE.Vec d × PDE.Vec d)` for standard topology infrastructure.

## Implementation note

The transported product metric supplies only the ordinary topology and
uniformity used by sets, continuity, and compactness. It is not the
manuscript's Euclidean kinetic geometry; Euclidean norms and balls must use
the explicit `PDEFoundation` API.
-/
@[expose] public section
namespace HypoellipticAleksandrov
/-- A point of kinetic spacetime in dimension `d`. -/
@[ext]
structure KineticPoint (d : ℕ) where
  /-- Time coordinate. -/
  time : ℝ
  /-- Position coordinate. -/
  position : PDE.Vec d
  /-- Velocity coordinate. -/
  velocity : PDE.Vec d
/-- The explicit coordinate equivalence with the standard nested product carrier. -/
def KineticPoint.equivProd (d : ℕ) :
    KineticPoint d ≃ ℝ × (PDE.Vec d × PDE.Vec d) where
  toFun z := (z.time, (z.position, z.velocity))
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by
    ext <;> rfl
  right_inv z := by
    rcases z with ⟨t, x, v⟩
    rfl
/-- The standard product metric transported to the explicit coordinate carrier.

This is only topology and uniformity infrastructure, not manuscript round
Euclidean geometry. -/
instance (d : ℕ) : MetricSpace (KineticPoint d) :=
  MetricSpace.induced (KineticPoint.equivProd d)
    (KineticPoint.equivProd d).injective inferInstance

end HypoellipticAleksandrov

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.PDEFoundation.Ambient.EuclideanNorm ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/
@[expose] public section
open scoped BigOperators
namespace PDE
/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.HypoellipticAleksandrov.Ambient.MatrixContraction ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Entrywise matrix contraction

This module defines the entrywise Frobenius contraction used by the
time--velocity operator and relates it to matrix trace when the second matrix
is symmetric.
-/
@[expose] public section
open scoped BigOperators
namespace HypoellipticAleksandrov
/-- The entrywise Frobenius contraction of two real square matrices. -/
def matrixContraction {d : ℕ} (A H : PDE.Mat d) : ℝ :=
  ∑ i, ∑ j, A i j * H i j

end HypoellipticAleksandrov

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.PDEFoundation.Ambient.Basis ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/
@[expose] public section
namespace PDE
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.PDEFoundation.Sobolev.ClassicalGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Classical gradients in the native ambient space

The inherited norm on `PDE.Vec d` is the finite-product supremum norm. This
file packages the coordinate gradient of a classically differentiable scalar
function as a native vector and relates directional derivatives to the
explicit Euclidean dot product. Quantitative PDE estimates should use the
resulting Euclidean Cauchy--Schwarz inequality, not the operator norm induced
by the inherited product norm.
-/
@[expose] public section
namespace PDE
/-- The coordinate gradient of a scalar function, expressed in the native
vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.HypoellipticAleksandrov.Parabolic.KineticClassical ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Classical kinetic product API

This module fixes the product-cylinder geometry, anisotropic classical
regularity, and plus-sign kinetic operator used in the time-velocity estimates.  The kinetic points
retain their explicit time, position, and velocity fields; product sets are transported only through
`KineticPoint.homeomorphProd`.

No maximum theorem is proved here.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic

/-- The time derivative with position and velocity held fixed. -/
def kineticTimeDerivative {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time
/-- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Vec d :=
  PDE.classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

/-- The velocity Hessian indexed as `D_i(D_j u)`. -/
def kineticVelocityHessian {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Mat d :=
  fun i j =>
    (fderiv ℝ (fun v : PDE.Vec d =>
      PDE.classicalGradient (fun w : PDE.Vec d => u ⟨z.time, z.position, w⟩) v)
      z.velocity (PDE.basisVec i)) j

namespace IsKineticC112On

end IsKineticC112On

end HypoellipticAleksandrov.Parabolic

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.HypoellipticAleksandrov.KineticAleksandrov.Operator ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Kinetic Aleksandrov operators

This module records the three operator surfaces used by the kinetic
Aleksandrov source.  `backwardOperator` is the full kinetic operator
`∂ₜ + v · ∇ₓ - A : Dᵥ²`, while `transportedForwardOperator` is the forward
operator `∂σ + B : Dᵧ² + b(y) · ∇z`.

For the transported operator, `KineticPoint n` is read as the ordered triple
`(σ, y, z)`: its `position` field is the diffused `y` coordinate and its
`velocity` field is the transported `z` coordinate.  The derivative APIs are
the existing ones on `KineticPoint`; no second point or derivative hierarchy
is introduced.  The W/I domain and structural alternatives belong to a
separate setting conditions, not to these literal operator definitions.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov
open HypoellipticAleksandrov.Parabolic
/-- A full matrix coefficient depending on time, position, and velocity. -/
abbrev FullKineticCoefficient (d : ℕ) :=
  ℝ → PDE.Vec d → PDE.Vec d → PDE.Mat d
/-- Evaluation of a full kinetic coefficient at an explicit kinetic point. -/
def fullKineticCoefficientAt {d : ℕ} (A : FullKineticCoefficient d)
    (z : KineticPoint d) : PDE.Mat d :=
  A z.time z.position z.velocity

/-- The backward kinetic operator with full coefficient dependence. -/
def backwardOperator {d : ℕ} (A : FullKineticCoefficient d)
    (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  Parabolic.kineticTimeDerivative u z +
    PDE.vecDot z.velocity (Parabolic.kineticPositionGradient u z) -
      matrixContraction (fullKineticCoefficientAt A z)
        (Parabolic.kineticVelocityHessian u z)

end HypoellipticAleksandrov.KineticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.HypoellipticAleksandrov.Geometry.KineticPointMeasure ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Lebesgue measure on kinetic points

The coordinate equivalence identifies kinetic volume with product Lebesgue
measure in the literal order (t,x,v), without any normalization factor.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov
open MeasureTheory
/-- Borel measurable sets for the coordinate product topology on kinetic points. -/
@[expose] instance KineticPoint.instMeasurableSpace (d : ℕ) :
    MeasurableSpace (KineticPoint d) := borel (KineticPoint d)
set_option linter.unusedVariables false in
axiom _root_.HypoellipticAleksandrov.KineticPoint.instBorelSpace : ∀ (d : ℕ), BorelSpace (HypoellipticAleksandrov.KineticPoint d)
attribute [instance] _root_.HypoellipticAleksandrov.KineticPoint.instBorelSpace
/-- Product Lebesgue measure transported to kinetic points in the order (t,x,v). -/
@[expose] instance KineticPoint.instMeasureSpace (d : ℕ) : MeasureSpace (KineticPoint d) where
  volume := Measure.map (KineticPoint.equivProd d).symm
    (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))

end HypoellipticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v897ffa09047a.HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Proposed Section 6 setting

Predicates for companion paper, Section 9.
The operator, affine map, quasi-distance and forward stack are reused from
KineticAleksandrov.Operator and Geometry with their usual meanings.
Smoothness is expressed in the existing product coordinates, not through a
new differential structure on KineticPoint.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory
open scoped ENNReal

/-- The localised positive source in e:amp, including its superlevel indicator. -/
def localizedSource {d : ℕ} (A : FullKineticCoefficient d)
    (psi u : KineticPoint d → ℝ) : KineticPoint d → ℝ :=
  {P | u P < psi P}.indicator (fun P => max (backwardOperator A psi P) 0)

end HypoellipticAleksandrov.KineticAleksandrov.Holder

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_463c4aa97de684f5f4da_NearFullSourceNorm ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Quantitative source localization to the strict sublevel set -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory
open scoped ENNReal
set_option linter.unusedVariables false in
/-- A bounded localized positive source is controlled by the strict-sublevel volume. -/
theorem localizedSource_norm_le_sublevel_volume {d : ℕ} (A : FullKineticCoefficient d)
    {psi u : KineticPoint d → ℝ} {Q : Set (KineticPoint d)} (hQ : IsOpen Q)
    (hQfinite : volume Q ≠ ⊤) (hpsi : ContinuousOn psi Q) (hu : ContinuousOn u Q)
    (hopm : Measurable (backwardOperator A psi)) (ell B p : ℝ)
    (hB : 0 ≤ B) (hp : 1 ≤ p) (hlevel : ∀ P ∈ Q, psi P ≤ ell)
    (hop : ∀ᵐ P ∂(volume.restrict Q), |backwardOperator A psi P| ≤ B) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_Holder_localizedSource_aestronglyMeasurable : ∀ {d : ℕ} (A : HypoellipticAleksandrov.KineticAleksandrov.FullKineticCoefficient d)
      {psi u : HypoellipticAleksandrov.KineticPoint d → ℝ}
      {Q : Set (HypoellipticAleksandrov.KineticPoint d)},
      IsOpen Q →
        ContinuousOn psi Q →
          ContinuousOn u Q →
            Measurable (HypoellipticAleksandrov.KineticAleksandrov.backwardOperator A psi) →
              MeasureTheory.AEStronglyMeasurable
                (HypoellipticAleksandrov.KineticAleksandrov.Holder.localizedSource A psi u)
                (MeasureTheory.MeasureSpace.volume.restrict Q))
    :
    (eLpNorm (localizedSource A psi u) (ENNReal.ofReal p) (volume.restrict Q)).toReal ≤
      B * (volume ({P | u P < ell} ∩ Q)).toReal ^ (1 / p) := by
  let E := {P | u P < ell} ∩ Q
  have hE : MeasurableSet E := by
    simpa only [E, Set.preimage, mem_Iio, inter_comm] using
      (hu.isOpen_inter_preimage hQ (isOpen_Iio (a := ell))).measurableSet
  have hm := h_HypoellipticAleksandrov_KineticAleksandrov_Holder_localizedSource_aestronglyMeasurable A hQ hpsi hu hopm
  have hbound : ∀ᵐ P ∂(volume.restrict Q),
      ‖localizedSource A psi u P‖ ≤ ‖E.indicator (fun _ => B) P‖ := by
    filter_upwards [ae_restrict_mem hQ.measurableSet, hop] with P hP hb
    by_cases hs : u P < psi P
    · have hPE : P ∈ E := ⟨hs.trans_le (hlevel P hP), hP⟩
      rw [indicator_of_mem hPE]
      simp only [localizedSource, indicator, mem_ofPred_eq, hs, ite_true, Real.norm_eq_abs,
        abs_of_nonneg hB, abs_of_nonneg (le_max_right (backwardOperator A psi P) 0)]
      exact max_le ((le_abs_self _).trans hb) hB
    · simp only [localizedSource, indicator, mem_ofPred_eq, hs, ite_false, norm_zero]
      exact norm_nonneg _
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hnorm := eLpNorm_mono_ae (p := ENNReal.ofReal p) hm hbound
  rw [eLpNorm_indicator_const hE.nullMeasurableSet
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top] at hnorm
  have hmeasure : (volume.restrict Q) E = volume E := by
    rw [Measure.restrict_apply hE, inter_eq_left.mpr inter_subset_right]
  rw [hmeasure, ENNReal.toReal_ofReal hp0.le] at hnorm
  have hEfinite : volume E ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right hQfinite
  have hright : ‖B‖ₑ * volume E ^ (1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hp0.le) hEfinite)
  have hreal := ENNReal.toReal_mono hright hnorm
  simpa only [ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hB,
    ENNReal.toReal_ofReal hB, ← ENNReal.toReal_rpow] using hreal
end HypoellipticAleksandrov.KineticAleksandrov.Holder
