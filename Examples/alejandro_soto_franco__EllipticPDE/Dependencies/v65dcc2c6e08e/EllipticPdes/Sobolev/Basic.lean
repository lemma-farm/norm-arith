/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.TestFunction
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# H¹ and H₀¹ as weak-derivative Hilbert spaces

We realise `W^{1,2}(Ω)` as the **graph of the weak-gradient operator** inside the Hilbert space
`L²(Ω) × (L²(Ω))ᵈ` (encoded as `PiLp 2` over `Fin (d+1)`: coordinate `0` is the function,
coordinate `i.succ` the `i`-th weak partial). The weak-gradient relation is orthogonality to a
family of explicit "constraint vectors", so `W^{1,2}` is an orthogonal complement: closed,
complete, and a real Hilbert space with no further work.
-/
@[expose] public section
open MeasureTheory
open scoped RealInnerProductSpace ENNReal Distributions
noncomputable section
namespace MeasureTheory.L2
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
end MeasureTheory.L2
namespace EllipticPdes.Sobolev
variable {d : ℕ}
/-- The real `L²` space on a domain `Ω ⊆ ℝ^d` (restricted Lebesgue measure). -/
abbrev L2D (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  Lp ℝ 2 (volume.restrict Ω)
/-- Ambient Hilbert space for the graph encoding: a function value together with `d` gradient
components, with the ℓ² (H¹) inner product. Coordinate `0` is the function; coordinate `i.succ`
is the `i`-th weak partial derivative. -/
abbrev H1amb (Ω : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  PiLp 2 (fun _ : Fin (d + 1) => L2D Ω)
namespace H1amb
variable {Ω : Set (EuclideanSpace ℝ (Fin d))}
end H1amb
def partialD (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
def IsTestFn (Ω : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω
namespace IsTestFn
variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
lemma continuous (h : IsTestFn Ω φ) : Continuous φ := h.1.continuous
lemma continuous_partialD (h : IsTestFn Ω φ) (i : Fin d) : Continuous (partialD i φ) :=
  ((h.1.continuous_fderiv (by simp)).clm_apply continuous_const)
/-- Each partial derivative of a test function has compact support. -/
lemma hasCompactSupport_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    HasCompactSupport (partialD i φ) := by
  exact h.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
lemma memLp (h : IsTestFn Ω φ) : MemLp φ 2 (volume.restrict Ω) :=
  h.continuous.memLp_of_hasCompactSupport h.2.1
alias mem_lp := memLp
/-- Each partial derivative of a test function lies in `L²(Ω)`. -/
lemma memLp_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    MemLp (partialD i φ) 2 (volume.restrict Ω) :=
  (h.continuous_partialD i).memLp_of_hasCompactSupport (h.hasCompactSupport_partialD i)
/-- The `L²(Ω)` class of a test function. -/
def testCls (h : IsTestFn Ω φ) : L2D Ω := h.memLp.toLp φ
/-- The `L²(Ω)` class of the `i`-th partial derivative of a test function. -/
def partialCls (h : IsTestFn Ω φ) (i : Fin d) : L2D Ω :=
  (h.memLp_partialD i).toLp (partialD i φ)
def constraintVec (h : IsTestFn Ω φ) (i : Fin d) : H1amb Ω :=
  PiLp.single 2 0 (h.partialCls i) + PiLp.single 2 i.succ h.testCls
def testGraph (h : IsTestFn Ω φ) : H1amb Ω :=
  WithLp.toLp 2 (Fin.cons h.testCls (fun i => h.partialCls i))
end IsTestFn
def constraintSet (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H1amb Ω) :=
  { w | ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ) (i : Fin d),
      w = h.constraintVec i }
/-- `W^{1,2}(Ω)`: functions paired with their weak `L²` gradient, realised as the
orthogonal complement of the constraint vectors inside the ambient Hilbert space. As an
orthogonal complement it is automatically a closed, complete, real Hilbert space. -/
def W12 (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) :=
  (Submodule.span ℝ (constraintSet Ω))ᗮ
/-- `W^{1,2}(Ω)` is complete, being an orthogonal complement in a Hilbert space. -/
instance instCompleteSpaceW12 (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (W12 Ω) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℝ (constraintSet Ω))ᗮ)
namespace W12
variable {Ω : Set (EuclideanSpace ℝ (Fin d))}
end W12
def testGraphSet (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H1amb Ω) :=
  { U | ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ), U = h.testGraph }
def H01 (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) :=
  (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure
/-- `H₀¹(Ω)` is complete, being a topological closure in a Hilbert space. -/
instance instCompleteSpaceH01 (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    CompleteSpace (H01 Ω) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure)
namespace H01
variable {Ω : Set (EuclideanSpace ℝ (Fin d))}
end H01
end EllipticPdes.Sobolev
