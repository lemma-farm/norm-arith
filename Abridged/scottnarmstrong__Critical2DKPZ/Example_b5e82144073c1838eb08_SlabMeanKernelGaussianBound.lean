module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.Site ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The square lattice `ℤ²`. -/
@[reducible] def Site := Fin 2 → ℤ
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.SrwStep ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The four steps `± e₁, ± e₂` of the simple symmetric random walk on `ℤ²`. -/
def srwStep : Fin 4 → Site :=
  ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]]
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.WalkPosition ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Position after `j` steps of the walk started at `w` with step sequence `s`
(for `j ≥ n` this is the endpoint). -/
def walkPosition (w : Site) {n : ℕ} (s : Fin n → Fin 4) (j : ℕ) : Site :=
  w + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), srwStep (s i)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.SrwKernel ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Transition probability `q_n(z) = P₀(S_n = z)` of the simple random walk. -/
def srwKernel (n : ℕ) (z : Site) : ℝ :=
  ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * if walkPosition 0 s n = z then 1 else 0
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.KernelBridge ====
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
# Identifying the path sum with the recursive simple walk kernel

The four step labels enumerate the two signed coordinate directions. Splitting a
word at its final letter gives the same recursion as `LatticeProb.srwHeat`.
-/
@[expose] public section
namespace Critical2DKPZ

set_option linter.unusedVariables false in
axiom _root_.Critical2DKPZ.srwKernel_zero : ∀ (z : Critical2DKPZ.Site), Critical2DKPZ.srwKernel 0 z = if z = 0 then 1 else 0

end Critical2DKPZ

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.Plane ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The plane `ℝ²`, with its Euclidean structure. -/
@[reducible] def Plane := EuclideanSpace ℝ (Fin 2)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.SiteToPlane ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The point of `ℝ²` with the coordinates of a lattice site. -/
def siteToPlane (z : Site) : Plane :=
  WithLp.toLp 2 fun i => (z i : ℝ)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.NearestEven ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- A nearest point `[x]` of the even lattice `{z : z₁ + z₂ ∈ 2ℤ}` (§1.1). Writing
`x = (u + v, u − v)`, the even lattice is `{(a + b, a − b) : a, b ∈ ℤ}` and
`|x − (a + b, a − b)|² = 2 ((u − a)² + (v − b)²)`; we take `a = round u`, `b = round v`
(ties broken towards `+∞`, the fixed tie-breaking rule required by the source). -/
def nearestEven (x : Plane) : Site :=
  let a := round ((x 0 + x 1) / 2)
  let b := round ((x 0 - x 1) / 2)
  ![a + b, a - b]
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.LatticePoint ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The lattice point `[√(N/2) x]` representing `x` at scale `N` (§1.1). -/
def latticePoint (N : ℕ) (x : Plane) : Site :=
  nearestEven (Real.sqrt (N / 2) • x)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.ReplicaOverlap ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Expected replica overlap `R_N = ∑_{n=1}^N P(S_{2n} = 0)` (§1.1). -/
def replicaOverlap (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, srwKernel (2 * n) 0
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.CriticalSigmaSq ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The critical-window variance `σ_N² = R_N⁻¹ (1 + ϑ / log N)` (§1.1). -/
def criticalSigmaSq (ϑ : ℝ) (N : ℕ) : ℝ :=
  (1 + ϑ / Real.log N) / replicaOverlap N
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.CriticalBeta ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Critical disorder strength `β_N = √(log(1 + σ_N²)) ≥ 0`, the nonnegative solution of
`e^{β_N²} − 1 = σ_N²` (§1.1) whenever `σ_N² ≥ 0`; this holds as soon as `N ≥ 1` and
`log N > |ϑ|` (`criticalBeta_spec`). For the finitely many other `N` the source's `β_N` is undefined
and the value is a junk value of Mathlib's conventions (`x / 0 = 0`, `log (−x) = log x`, `√` of a
negative number is `0`): it is `0` for `N = 0` and when `σ_N² ∈ [−2, 0]`, and positive for `N = 1` and
when `σ_N² < −2`. Statements about `β_N` are asymptotic in `N` or restricted to such `N`. -/
def criticalBeta (ϑ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (1 + criticalSigmaSq ϑ N))
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Analysis.Lattice.Sampling ====
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
/-! Sampling each lattice cell at its representative gives a measurable map that converges pointwise to the identity as the mesh tends to zero. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Critical2DKPZ
/-- The continuum location of the lattice site at diffusive scale `N`. -/
def latticeRepresentative (N : ℕ) (z : Site) : Plane :=
  (Real.sqrt (N / 2))⁻¹ • siteToPlane z
/-- Each point is mapped to the representative of its nearest-even-lattice cell. -/
def cellSample (N : ℕ) (x : Plane) : Plane := latticeRepresentative N (latticePoint N x)

end Critical2DKPZ
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.EvenCeil ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The even integer approximation `[t] = 2 ⌈t / 2⌉` of `t ≥ 0` (§1.1); it is `0` for `t ≤ 0`. -/
def evenCeil (t : ℝ) : ℕ :=
  2 * ⌈t / 2⌉₊
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.Disorder ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- A disorder configuration: a real number `ω (j, z)` for every time `j ∈ ℕ` and site `z ∈ ℤ²`. -/
@[reducible] def Disorder := ℕ × Site → ℝ
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.PointToPoint ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Point-to-point partition function `Z^β_{a,a+n}(w, z)` (§1.1): the walk starts at `w` at
time `a`, makes `n` steps, and is weighted by the disorder at times `a+1, …, a+n`. -/
def pointToPoint (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) : ℝ :=
  ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
    Real.exp (∑ j ∈ Finset.Icc 1 n, (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2)) *
    if walkPosition w s n = z then 1 else 0
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.RescaledP2P ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Rescaled point-to-point partition function `𝒵^{ϑ,(N)}_{s,t}(x, y)` (§1.1), as a density on
`ℝ² × ℝ²`; it uses the walk from time `[Ns]` to time `[Nt]` (for `s > t` the natural subtraction gives
zero steps, a value no statement uses). -/
def rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ) (p : Plane × Plane) (ω : Disorder) : ℝ :=
  (N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t) - evenCeil (N * s))
    (latticePoint N p.1) (latticePoint N p.2) ω
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.DisorderLaw ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The law `ℙ` of the disorder: the `ω (j, z)` are independent standard Gaussian variables. -/
def disorderLaw : Measure Disorder :=
  Measure.infinitePi fun _ : ℕ × Site => gaussianReal 0 1
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.SHF.Limit.SlabMean ====
public section
/-
Copyright 2026 Scott Armstrong. All rights reserved.
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
/-! # Annealed polymer density on a time slab -/
@[expose] public section
open MeasureTheory
noncomputable section
namespace Critical2DKPZ.SHF.Limit
/-- The mean density of the polymer measure on the slab `(t, t']`: the rescaled walk kernel. -/
def slabMeanKernel (ϑ : ℝ) (N : ℕ) (t t' : ℝ) (w y : Plane) : ℝ :=
  ∫ ω, rescaledP2P ϑ N t t' (w, y) ω ∂disorderLaw

end Critical2DKPZ.SHF.Limit
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_b5e82144073c1838eb08_SlabMeanKernelGaussianBound ====
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
/-! # Uniform Gaussian envelope for a mean slab kernel -/
@[expose] public section
open Critical2DKPZ.SHF.Limit

namespace Critical2DKPZ.SHF.Flow
set_option linter.unusedVariables false in
/-- A positive macroscopic slab has a Gaussian bound uniform over every lattice scale. -/
theorem exists_slabMeanKernel_gaussianBound (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {v : ℝ} (hv : 0 < v) 
    (h_Critical2DKPZ_evenCeil_mono : Monotone Critical2DKPZ.evenCeil)
    (h_Critical2DKPZ_SHF_Limit_slabMeanKernel_eq_srwKernel : ∀ (ϑ : ℝ) (N : ℕ) (t t' : ℝ) (w y : Critical2DKPZ.Plane),
      Critical2DKPZ.SHF.Limit.slabMeanKernel ϑ N t t' w y =
        (↑N : ℝ) / 4 *
          Critical2DKPZ.srwKernel
            (Critical2DKPZ.evenCeil ((↑N : ℝ) * t') - Critical2DKPZ.evenCeil ((↑N : ℝ) * t))
            (Critical2DKPZ.latticePoint N y - Critical2DKPZ.latticePoint N w))
    (h_Critical2DKPZ_dist_cellSample_le : ∀ {N : ℕ},
      0 < N →
        ∀ (x : Critical2DKPZ.Plane), Dist.dist (Critical2DKPZ.cellSample N x) x ≤ (√((↑N : ℝ) / 2))⁻¹)
    (h_Critical2DKPZ_evenCeil_duration_error : ∀ {s t : ℝ},
      0 ≤ s →
        0 ≤ t → |(↑(Critical2DKPZ.evenCeil t) : ℝ) - (↑(Critical2DKPZ.evenCeil s) : ℝ) - (t - s)| < 2)
    (h_Critical2DKPZ_srwKernel_nonneg : ∀ (n : ℕ) (z : Critical2DKPZ.Site), 0 ≤ Critical2DKPZ.srwKernel n z)
    (h_Critical2DKPZ_SHF_Moments_srwKernel_gaussianBound_all_times : ∃ (C : ℝ) (c : ℝ),
      0 < C ∧
        0 < c ∧
          ∀ (n : ℕ) (z : Critical2DKPZ.Site),
            Critical2DKPZ.srwKernel n z ≤
              C / ((↑n : ℝ) + 1) * Real.exp (-c * ‖Critical2DKPZ.siteToPlane z‖ ^ 2 / ((↑n : ℝ) + 1)))
    :
    ∃ C c : ℝ, 0 < c ∧ ∀ N : ℕ, ∀ x y : Plane,
      |slabMeanKernel ϑ N t (t + v) x y| ≤ C * Real.exp (-c * ‖y - x‖ ^ 2) := by
  obtain ⟨Cw, cw, hCw, hcw, hwalk⟩ := h_Critical2DKPZ_SHF_Moments_srwKernel_gaussianBound_all_times
  let c := cw / (4 * (v + 3))
  refine ⟨Cw / v * Real.exp (4 * cw), c, ?_, ?_⟩
  · dsimp [c]
    positivity
  · intro N x y
    by_cases hN : N = 0
    · subst N
      rw [h_Critical2DKPZ_SHF_Limit_slabMeanKernel_eq_srwKernel]
      simp
      exact le_of_lt (mul_pos (mul_pos (div_pos hCw hv) (Real.exp_pos _))
        (Real.exp_pos _))
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      let m := evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t)
      let z := latticePoint N y - latticePoint N x
      let r := latticeRepresentative N z
      have hmono : evenCeil ((N : ℝ) * t) ≤ evenCeil ((N : ℝ) * (t + v)) :=
        h_Critical2DKPZ_evenCeil_mono (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      have hmcast : (m : ℝ) =
          (evenCeil ((N : ℝ) * (t + v)) : ℝ) - evenCeil ((N : ℝ) * t) := by
        simp only [m, Nat.cast_sub hmono]
      have hround := h_Critical2DKPZ_evenCeil_duration_error
        (s := (N : ℝ) * t) (t := (N : ℝ) * (t + v)) (by positivity) (by positivity)
      have hclock : |(m : ℝ) - (N : ℝ) * v| < 2 := by
        rw [hmcast]
        convert hround using 1
        ring_nf
      have hmupper : (m : ℝ) + 1 ≤ (N : ℝ) * v + 3 := by
        have h := (abs_lt.mp hclock).2
        linarith
      have hNcast : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
      have hcoeff : (N : ℝ) / (4 * ((m : ℝ) + 1)) ≤ 1 / v := by
        by_cases hlarge : 4 ≤ (N : ℝ) * v
        · have hmlower : (N : ℝ) * v / 2 ≤ (m : ℝ) + 1 := by
            have h := (abs_lt.mp hclock).1
            linarith
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith only [hmlower]
        · have hNvsmall : (N : ℝ) * v < 4 := lt_of_not_ge hlarge
          have hone : 1 ≤ (m : ℝ) + 1 := by
            have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
            linarith
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith only [hNvsmall, hone]
      have hrrep : latticeRepresentative N z = cellSample N y - cellSample N x := by
        simp only [z, latticeRepresentative, cellSample]
        rw [← smul_sub]
        congr 1
        ext i
        simp [siteToPlane]
      have hdist : ‖(y - x) - r‖ ≤ 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
        change ‖(y - x) - latticeRepresentative N z‖ ≤ _
        rw [hrrep]
        have hrewrite : (y - x) - (cellSample N y - cellSample N x) =
            (y - cellSample N y) - (x - cellSample N x) := by abel
        rw [hrewrite]
        calc
          ‖(y - cellSample N y) - (x - cellSample N x)‖ ≤
              ‖y - cellSample N y‖ + ‖x - cellSample N x‖ := norm_sub_le _ _
          _ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ +
              (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
            have hy := h_Critical2DKPZ_dist_cellSample_le hNpos y
            have hx := h_Critical2DKPZ_dist_cellSample_le hNpos x
            rw [dist_comm, dist_eq_norm] at hy hx
            exact add_le_add hy hx
          _ = _ := by ring
      have hmeshSq : (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 = 2 / (N : ℝ) := by
        rw [inv_pow, Real.sq_sqrt (by positivity)]
        field_simp
      have hrepSq : ‖r‖ ^ 2 ≥ ‖y - x‖ ^ 2 / 2 - 8 / (N : ℝ) := by
        have htri : ‖y - x‖ ≤ ‖r‖ + 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
          calc
            ‖y - x‖ = ‖((y - x) - r) + r‖ := by congr 1; abel
            _ ≤ ‖(y - x) - r‖ + ‖r‖ := norm_add_le _ _
            _ ≤ 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ + ‖r‖ := add_le_add hdist le_rfl
            _ = _ := by ring
        have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
        have hyoung : (‖r‖ + 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹) ^ 2 ≤
            2 * ‖r‖ ^ 2 + 8 * (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 := by
          nlinarith only [sq_nonneg (‖r‖ -
            2 * (Real.sqrt ((N : ℝ) / 2))⁻¹)]
        have hcombined : ‖y - x‖ ^ 2 ≤
            2 * ‖r‖ ^ 2 + 8 * (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 := le_trans hsq hyoung
        rw [hmeshSq] at hcombined
        rw [show 8 * (2 / (N : ℝ)) = 16 / (N : ℝ) by ring] at hcombined
        have hhalf : ‖y - x‖ ^ 2 / 2 ≤ ‖r‖ ^ 2 + 8 / (N : ℝ) := by
          calc
            ‖y - x‖ ^ 2 / 2 ≤ (2 * ‖r‖ ^ 2 + 16 / (N : ℝ)) / 2 :=
              div_le_div_of_nonneg_right hcombined (by norm_num)
            _ = ‖r‖ ^ 2 + 8 / (N : ℝ) := by ring
        linarith
      have hroot : 0 < Real.sqrt ((N : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
      have hsite : siteToPlane z = Real.sqrt ((N : ℝ) / 2) • r := by
        dsimp [r, latticeRepresentative]
        rw [smul_smul, mul_inv_cancel₀ hroot.ne', one_smul]
      have hsiteSq : ‖siteToPlane z‖ ^ 2 = ((N : ℝ) / 2) * ‖r‖ ^ 2 := by
        rw [hsite, norm_smul, Real.norm_eq_abs, abs_of_pos hroot, mul_pow,
          Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
      let α := cw * (N : ℝ) / (2 * ((m : ℝ) + 1))
      have hαnonneg : 0 ≤ α := by dsimp [α]; positivity
      have hαlower : cw / (2 * (v + 3)) ≤ α := by
        dsimp [α]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [hmupper, hNcast, hcw.le, hv.le]
      have hαmesh : α * (8 / (N : ℝ)) ≤ 4 * cw := by
        have hone : 1 ≤ (m : ℝ) + 1 := by
          have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        have heq : α * (8 / (N : ℝ)) = 4 * cw / ((m : ℝ) + 1) := by
          dsimp [α]
          field_simp
          ring
        rw [heq, div_le_iff₀ (by positivity)]
        nlinarith only [hone, hcw.le]
      have hαhalf : c ≤ α / 2 := by
        calc
          cw / (4 * (v + 3)) = (cw / (2 * (v + 3))) * (1 / 2) := by field_simp; ring
          _ ≤ α * (1 / 2) := mul_le_mul_of_nonneg_right hαlower (by norm_num)
          _ = α / 2 := by ring
      have hαd : c * ‖y - x‖ ^ 2 ≤ α * ‖y - x‖ ^ 2 / 2 := by
        have h := mul_le_mul_of_nonneg_right hαhalf (sq_nonneg ‖y - x‖)
        nlinarith only [h]
      have hexpArg : -(cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) ≤
          4 * cw - c * ‖y - x‖ ^ 2 := by
        have harg : cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1) = α * ‖r‖ ^ 2 := by
          rw [hsiteSq]
          dsimp [α]
          field_simp
        have hmain := mul_le_mul_of_nonneg_left hrepSq hαnonneg
        rw [harg]
        rw [mul_sub] at hmain
        nlinarith only [hmain, hαmesh, hαd]
      have hexp : Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) ≤
          Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2) := by
        have hargForm : -cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1) =
            -(cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) := by ring
        rw [hargForm]
        calc
          Real.exp (-(cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1))) ≤
              Real.exp (4 * cw - c * ‖y - x‖ ^ 2) := Real.exp_le_exp.mpr hexpArg
          _ = Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
      have hformula : slabMeanKernel ϑ N t (t + v) x y =
          ((N : ℝ) / 4) * srwKernel m z := by
        rw [h_Critical2DKPZ_SHF_Limit_slabMeanKernel_eq_srwKernel]
      rw [hformula, abs_of_nonneg (mul_nonneg (by positivity) (h_Critical2DKPZ_srwKernel_nonneg _ _))]
      calc
        ((N : ℝ) / 4) * srwKernel m z ≤
          ((N : ℝ) / 4) * (Cw / ((m : ℝ) + 1) *
            Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact hwalk m z
        _ ≤ (Cw / v) * (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) := by
          have hcoef' : (N : ℝ) / 4 * (Cw / ((m : ℝ) + 1)) ≤ Cw / v := by
            rw [show (N : ℝ) / 4 * (Cw / ((m : ℝ) + 1)) =
              Cw * ((N : ℝ) / (4 * ((m : ℝ) + 1))) by field_simp]
            calc
              Cw * ((N : ℝ) / (4 * ((m : ℝ) + 1))) ≤ Cw * (1 / v) :=
                mul_le_mul_of_nonneg_left hcoeff hCw.le
              _ = Cw / v := by ring
          calc
            ((N : ℝ) / 4) * (Cw / ((m : ℝ) + 1) *
                Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1))) ≤
                ((N : ℝ) / 4 * (Cw / ((m : ℝ) + 1))) *
                  (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) := by
              calc
                _ = ((N : ℝ) / 4 * (Cw / ((m : ℝ) + 1))) *
                    Real.exp (-cw * ‖siteToPlane z‖ ^ 2 / ((m : ℝ) + 1)) := by ring
                _ ≤ ((N : ℝ) / 4 * (Cw / ((m : ℝ) + 1))) *
                    (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) :=
                  mul_le_mul_of_nonneg_left hexp (by positivity)
            _ ≤ (Cw / v) * (Real.exp (4 * cw) * Real.exp (-c * ‖y - x‖ ^ 2)) :=
              mul_le_mul_of_nonneg_right hcoef' (by positivity)
        _ = (Cw / v * Real.exp (4 * cw)) * Real.exp (-c * ‖y - x‖ ^ 2) := by ring
end Critical2DKPZ.SHF.Flow
end
