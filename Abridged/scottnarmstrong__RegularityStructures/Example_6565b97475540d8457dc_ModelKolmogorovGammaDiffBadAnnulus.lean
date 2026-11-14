module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.MeanInequalitiesPow

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Analysis.Parabolic.Basic ====
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
/-- The parabolic size `‖z‖_𝔰 = |z₀|^{1/2} + ∑ᵢ |zᵢ|` for the scaling `𝔰 = (2, 1, 1, 1)`. -/
def parabolicNorm (z : ParabolicSpace) : ℝ := Real.sqrt |z.1| + ∑ i, |z.2 i|

end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovHSParabolicGrid ====
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
# Parabolic dyadic grids for the model Kolmogorov criterion

The covering argument of Hairer--Steele, arXiv:2301.10081v3, Proposition B.3,
uses the scaling dimension rather than the topological dimension. On the unit
space-time box the time mesh is `2^(-2n)` and the three spatial meshes are
`2^(-n)`. Thus the grid has at most `16 * 2^(5n)` points.

These grids are deterministic geometry, independent of any random-model or
pathwise-bound hypothesis.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- Indices of the anisotropic dyadic grid in the unit space-time box. -/
abbrev HSParabolicGridIndex (n : ℕ) :=
  Fin (2 ^ (2 * n) + 1) × (Fin 3 → Fin (2 ^ n + 1))

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovHSCompactNet ====
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
# Finite nets whose representatives remain inside the compact

Hairer--Steele, arXiv:2301.10081v3, Proposition B.3 assumes moment bounds
only at points of the compact. Replacing the compact by a containing box in
the stochastic hypotheses would strengthen the statement. Instead we retain
one representative of each occupied anisotropic grid cell. This construction
works for any subset of the unit box, including the empty set, and has the
same dimension-five cardinality bound as the ambient grid.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- Clipped dyadic cell index; clipping makes it defined on every real number. -/
def hsDyadicCellIndex (n : ℕ) (x : ℝ) : Fin (2 ^ n + 1) :=
  ⟨min (Nat.floor (x * (2 : ℝ) ^ n)) (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩
/-- The time-space cell index with the parabolic time refinement. -/
def hsParabolicCellIndex (n : ℕ) (x : ParabolicSpace) : HSParabolicGridIndex n :=
  (hsDyadicCellIndex (2 * n) x.1, fun j => hsDyadicCellIndex n (x.2 j))
/-- Occupied cells carry witnesses in the original set, not in a larger neighbourhood. -/
abbrev HSParabolicOccupiedCell (S : Set ParabolicSpace) (n : ℕ) :=
  {i : HSParabolicGridIndex n // ∃ x : S, hsParabolicCellIndex n x = i}

/-- A selected point of the original set in each occupied cell. -/
def hsParabolicCellRepresentative (S : Set ParabolicSpace) (n : ℕ)
    (i : HSParabolicOccupiedCell S n) : S := Classical.choose i.property

end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovHSCompactParent ====
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
# Parent cells for intrinsic parabolic nets

The occupied-cell nets used in Hairer--Steele, arXiv:2301.10081v3,
Proposition B.3 must be compatible across scales. Dyadic floor division
shows that a fine cell lies in one coarse cell. Hence each occupied fine
cell has an occupied parent, and the two selected representatives are
within the coarse parabolic mesh radius. No enlargement of the stochastic
index set is involved.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The coarse occupied cell of a chosen fine representative. -/
def hsParabolicCellParent (S : Set ParabolicSpace) (n : ℕ)
    (i : HSParabolicOccupiedCell S (n + 1)) : HSParabolicOccupiedCell S n :=
  ⟨hsParabolicCellIndex n (hsParabolicCellRepresentative S (n + 1) i),
    hsParabolicCellRepresentative S (n + 1) i, rfl⟩
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vd8f03ff7a94f.RegularityStructures.Probability.ModelKolmogorovGammaProductNet ====
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
# Product-net increments for Gamma chaining

At a fixed parabolic scale the two base points are selected independently from
the occupied cells of the compact.  The definitions below retain that product
net explicitly.  Their moment lemmas are the finite, source-facing part of the
annular argument: no model norm or random bound is used as a premise.
-/
@[expose] public noncomputable section
open MeasureTheory
open Filter
open scoped ENNReal NNReal Topology
namespace RegularityStructures
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
abbrev gammaCell (S : Set ParabolicSpace) (n : ℕ) :=
  HSParabolicOccupiedCell S n

/-!
The next three lemmas use the source estimates at exactly the representative
pairs selected by the net.  The endpoint estimates are kept separate because
the later telescoping proof must preserve both Chen channels.
-/

/-!
The parent-child decomposition is the deterministic telescope used to pass from
the finite product nets to a genuine two-base-point field.  The orientation of
the right-step definition is chosen so that the intermediate value has the
fine first endpoint and the fine second endpoint.
-/

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_6565b97475540d8457dc_ModelKolmogorovGammaDiffBadAnnulus ====
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
# Pathwise annular bounds for the difference `DΓ × DΓ` channel

The difference of two Chen products is a sum of two terms.  When both
coordinates belong to `DΓ`, one factor is controlled pathwise by the
deterministic model estimate and the other by the pathwise difference
estimate.  The positive degree of the fine factor gives the geometric
endpoint reserve.  This is the difference analogue of the pathwise part of
Hairer [Hai14, (2.17)].
-/
@[expose] public noncomputable section
open Set
open scoped ENNReal
namespace RegularityStructures
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  

set_option linter.unusedVariables false in
private theorem gammaDiffBad_right_geometry
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (N k : ℕ) (hNk : N ≤ k) (a b : gammaCell S (k + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        20 / (2 : ℝ) ^ N) 
    (h_RegularityStructures_parabolicNorm_add_le : ∀ (z w : RegularityStructures.ParabolicSpace),
      RegularityStructures.parabolicNorm (z + w) ≤
        RegularityStructures.parabolicNorm z + RegularityStructures.parabolicNorm w)
    (h_RegularityStructures_hsParabolicCellParent_radius : ∀ (S : Set RegularityStructures.ParabolicSpace),
      (∀ x ∈ S, x.1 ∈ Set.Icc 0 1 ∧ ∀ (j : Fin 3), x.2 j ∈ Set.Icc 0 1) →
        ∀ (n : ℕ) (i : RegularityStructures.HSParabolicOccupiedCell S (n + 1)),
          RegularityStructures.parabolicNorm
              ((↑(RegularityStructures.hsParabolicCellRepresentative S n
                      (RegularityStructures.hsParabolicCellParent S n i)) :
                  RegularityStructures.ParabolicSpace) -
                (↑(RegularityStructures.hsParabolicCellRepresentative S (n + 1) i) :
                  RegularityStructures.ParabolicSpace)) ≤
            4 / 2 ^ n)
    (h_RegularityStructures_parabolicNorm_sub_comm : ∀ (z w : RegularityStructures.ParabolicSpace),
      RegularityStructures.parabolicNorm (z - w) = RegularityStructures.parabolicNorm (w - z))
    :
    parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ≤
        24 / (2 : ℝ) ^ N ∧
      parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b) -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        4 / (2 : ℝ) ^ k := by
  have hparent := h_RegularityStructures_hsParabolicCellParent_radius S hbox k b
  have hparent' : parabolicNorm
      (hsParabolicCellRepresentative S (k + 1) b -
        hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ≤
      4 / (2 : ℝ) ^ k := by
    rw [h_RegularityStructures_parabolicNorm_sub_comm]
    exact hparent
  constructor
  · calc
      _ = parabolicNorm
          ((hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k a) -
            hsParabolicCellRepresentative S (k + 1) b) +
            (hsParabolicCellRepresentative S (k + 1) b -
              hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k b))) := by
            congr 1
            abel
      _ ≤ 20 / (2 : ℝ) ^ N + 4 / (2 : ℝ) ^ k :=
        (h_RegularityStructures_parabolicNorm_add_le _ _).trans (add_le_add hnear hparent')
      _ ≤ 24 / (2 : ℝ) ^ N := by
        have hscale : 4 / (2 : ℝ) ^ k ≤ 4 / (2 : ℝ) ^ N := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (pow_le_pow_right₀ (by norm_num) hNk)
        calc
          20 / (2 : ℝ) ^ N + 4 / (2 : ℝ) ^ k ≤
              20 / (2 : ℝ) ^ N + 4 / (2 : ℝ) ^ N :=
            by simpa [add_comm] using
              (add_le_add_left hscale (20 / (2 : ℝ) ^ N))
          _ = 24 / (2 : ℝ) ^ N := by ring_nf
  · exact hparent

end RegularityStructures
end
