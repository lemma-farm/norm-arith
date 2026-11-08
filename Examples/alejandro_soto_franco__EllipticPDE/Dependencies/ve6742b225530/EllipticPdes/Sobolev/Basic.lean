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
lemma partialD_add {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (i : Fin d) :
    partialD i (φ + ψ) = partialD i φ + partialD i ψ := by
  funext x
  simp only [partialD, Pi.add_apply]
  rw [fderiv_add (hφ x) (hψ x), _root_.add_apply]
/-- `partialD` commutes with scalar multiplication on differentiable functions. -/
lemma partialD_const_smul {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (c : ℝ) (i : Fin d) :
    partialD i (c • φ) = c • partialD i φ := by
  funext x
  simp only [partialD, Pi.smul_apply]
  rw [fderiv_const_smul (hφ x) c, _root_.smul_apply]
/-- The classical partial of the zero function is zero. -/
lemma partialD_zero (i : Fin d) :
    partialD i (0 : EuclideanSpace ℝ (Fin d) → ℝ) = 0 := by
  funext x; simp [partialD]
/-- The topological support of a partial derivative sits inside the support of the
function: off `tsupport φ` the function is locally zero, so `fderiv` vanishes. -/
lemma tsupport_partialD_subset (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    tsupport (partialD i φ) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := φ) (EuclideanSpace.single i 1)
/-- A smooth, compactly supported test function whose support sits inside `Ω`. -/
def IsTestFn (Ω : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω
namespace IsTestFn
variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
/-- A test function is smooth. -/
lemma contDiff (h : IsTestFn Ω φ) : ContDiff ℝ (⊤ : ℕ∞) φ := h.1
/-- A test function has compact support. -/
lemma hasCompactSupport (h : IsTestFn Ω φ) : HasCompactSupport φ := h.2.1
/-- The support of a test function lies in the domain. -/
lemma tsupport_subset (h : IsTestFn Ω φ) : tsupport φ ⊆ Ω := h.2.2
/-- A test function is differentiable. -/
lemma differentiable (h : IsTestFn Ω φ) : Differentiable ℝ φ := h.1.differentiable (by simp)
/-- A test function is continuous. -/
lemma continuous (h : IsTestFn Ω φ) : Continuous φ := h.1.continuous
/-- Test functions are monotone in the domain: a test function of `Ω` is a test
function of any superset. -/
lemma mono {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))} (hsub : Ω ⊆ Ω')
    (h : IsTestFn Ω φ) : IsTestFn Ω' φ :=
  ⟨h.1, h.2.1, h.2.2.trans hsub⟩
/-- Each partial derivative of a test function is continuous. -/
lemma continuous_partialD (h : IsTestFn Ω φ) (i : Fin d) : Continuous (partialD i φ) :=
  ((h.1.continuous_fderiv (by simp)).clm_apply continuous_const)
/-- Each partial derivative of a test function has compact support. -/
lemma hasCompactSupport_partialD (h : IsTestFn Ω φ) (i : Fin d) :
    HasCompactSupport (partialD i φ) := by
  exact h.2.1.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
/-- `φ` being a test function is preserved under sums. -/
lemma add (h : IsTestFn Ω φ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (h' : IsTestFn Ω ψ) :
    IsTestFn Ω (φ + ψ) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, by
    refine Set.Subset.trans ?_ (Set.union_subset h.2.2 h'.2.2)
    refine (closure_mono (Function.support_add φ ψ)).trans ?_
    rw [closure_union]
    exact subset_rfl⟩
/-- `φ` being a test function is preserved under scalar multiplication. -/
lemma const_smul (h : IsTestFn Ω φ) (c : ℝ) : IsTestFn Ω (c • φ) :=
  ⟨h.1.const_smul c,
    h.2.1.of_isClosed_subset isClosed_closure (tsupport_smul_subset_right (fun _ => c) φ),
    (tsupport_smul_subset_right (fun _ => c) φ).trans h.2.2⟩
/-- The zero function is a test function. -/
lemma zero : IsTestFn Ω (0 : EuclideanSpace ℝ (Fin d) → ℝ) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩
/-- A test function lies in `L²(Ω)`. -/
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
/-- Simp lemma: `testGraph h 0 = testCls h`. -/
@[simp] lemma testGraph_zero (h : IsTestFn Ω φ) : h.testGraph 0 = h.testCls := by
  rw [testGraph, PiLp.toLp_apply, Fin.cons_zero]
/-- Simp lemma: `testGraph h i.succ = partialCls h i`. -/
@[simp] lemma testGraph_succ (h : IsTestFn Ω φ) (i : Fin d) :
    h.testGraph i.succ = h.partialCls i := by
  rw [testGraph, PiLp.toLp_apply, Fin.cons_succ]
/-- The graph embedding is additive: `(φ + ψ)` graphs to the sum of the graphs. -/
lemma testGraph_add (h : IsTestFn Ω φ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h' : IsTestFn Ω ψ) :
    h.testGraph + h'.testGraph = (h.add h').testGraph := by
  apply PiLp.ext
  intro j
  rw [PiLp.add_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [testGraph_zero, testCls]
    rw [← MemLp.toLp_add]
  · simp only [testGraph_succ, partialCls]
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq
      (partialD_add (h.1.differentiable (by simp)) (h'.1.differentiable (by simp)) i).symm)
/-- The graph embedding commutes with scalar multiplication. -/
lemma testGraph_const_smul (h : IsTestFn Ω φ) (c : ℝ) :
    c • h.testGraph = (h.const_smul c).testGraph := by
  apply PiLp.ext
  intro j
  rw [PiLp.smul_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [testGraph_zero, testCls]
    rw [← MemLp.toLp_const_smul]
  · simp only [testGraph_succ, partialCls]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq
      (partialD_const_smul (h.1.differentiable (by simp)) c i).symm)
/-- The graph of the zero function is the zero vector. -/
lemma testGraph_zero_fn : (IsTestFn.zero (Ω := Ω)).testGraph = 0 := by
  apply PiLp.ext
  intro j
  rw [PiLp.zero_apply]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [testGraph_zero, testCls, MemLp.toLp_zero]
  · simp only [testGraph_succ, partialCls]
    rw [MemLp.toLp_congr (IsTestFn.zero.memLp_partialD i) MemLp.zero
        (Filter.EventuallyEq.of_eq (partialD_zero i)), MemLp.toLp_zero]
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
/-- The test-function graphs already form a submodule: smooth compactly supported
functions are closed under sums and scalar multiples, and the graph embedding is linear.
This identifies `Submodule.span ℝ (testGraphSet Ω)` with `testGraphSet Ω` itself. -/
def testGraphSubmodule (Ω : Set (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (H1amb Ω) where
  carrier := testGraphSet Ω
  add_mem' := by
    rintro _ _ ⟨φ, h, rfl⟩ ⟨ψ, h', rfl⟩
    exact ⟨φ + ψ, h.add h', h.testGraph_add h'⟩
  zero_mem' := ⟨0, IsTestFn.zero, IsTestFn.testGraph_zero_fn.symm⟩
  smul_mem' := by
    rintro c _ ⟨φ, h, rfl⟩
    exact ⟨c • φ, h.const_smul c, h.testGraph_const_smul c⟩
/-- The span of the test-function graphs equals the test-function graphs. -/
lemma span_testGraphSet (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    Submodule.span ℝ (testGraphSet Ω) = testGraphSubmodule Ω :=
  Submodule.span_eq (testGraphSubmodule Ω)
/-- `H₀¹(Ω) = W₀^{1,2}(Ω)`: the closure of the smooth compactly supported functions
inside the ambient `H¹` space. As a topological closure it is automatically a closed,
complete, real Hilbert space. -/
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
