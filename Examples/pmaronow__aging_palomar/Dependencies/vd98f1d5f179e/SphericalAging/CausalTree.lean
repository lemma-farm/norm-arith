module
public import Mathlib
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
set_option autoImplicit false
public section
/-! Concrete ordered-tree Hilbert space from manuscript Section 7.
Every vertex has either zero or exactly `m` ordered children. Each tree carries
an actual completed tensor product of copies of `ℝ ⊕ L²((0,∞),du)`; their `ℓ²`
direct sum is the causal tree Hilbert space. No dynamical or geometric conclusion
is assumed in this construction.
-/
noncomputable section
open scoped TensorProduct InnerProductSpace ENNReal
open MeasureTheory UniformSpace
namespace SphericalAging.CausalTree
attribute [local instance] Classical.propDecidable
/-- Finite rooted ordered full `m`-ary trees. -/
inductive Tree (m : ℕ) : Type
  | leaf : Tree m
  | graft : (Fin m → Tree m) → Tree m
local instance (m : ℕ) : DecidableEq (Tree m) := Classical.decEq _
namespace Tree
variable {m : ℕ}
@[expose] def height : Tree m → ℕ :=
  Tree.rec 0 (fun _ heights => 1 + Finset.univ.sup heights)
theorem graft_injective : Function.Injective (@graft m) := fun _ _ h => graft.inj h
end Tree
/-- A complete real Hilbert space, bundled to permit recursion on a tree. -/
structure HilbertDatum where
  Carrier : Type
  group : NormedAddCommGroup Carrier
  inner : @InnerProductSpace ℝ Carrier _ group.toSeminormedAddCommGroup
  complete : @CompleteSpace Carrier group.toUniformSpace
attribute [instance] HilbertDatum.group HilbertDatum.inner HilbertDatum.complete
namespace HilbertDatum
@[expose, reducible] def real : HilbertDatum := ⟨ℝ, inferInstance, inferInstance, inferInstance⟩
/-- The completed, rather than merely algebraic, Hilbert tensor product. -/
@[expose, reducible] def tensor (A B : HilbertDatum) : HilbertDatum :=
  ⟨Completion (A.Carrier ⊗[ℝ] B.Carrier), inferInstance, inferInstance, inferInstance⟩
@[expose, reducible] def finiteTensor : (n : ℕ) → (Fin n → HilbertDatum) → HilbertDatum
  | 0, _ => real
  | n + 1, A => tensor (A 0) (finiteTensor n (fun i => A i.succ))
end HilbertDatum
/-- Brownian leaf factor, exactly `L²((0,∞),du)`, represented by restriction of Lebesgue measure. -/
@[expose] abbrev NoiseSpace := Lp ℝ 2 (volume.restrict (Set.Ioi (0 : ℝ)))
/-- Distinguished initial direction plus Brownian leaf factor, with the Hilbert product norm. -/
@[expose] abbrev LeafSpace := WithLp 2 (ℝ × NoiseSpace)
@[expose, reducible] def leafDatum : HilbertDatum := ⟨LeafSpace, inferInstance, inferInstance, inferInstance⟩
@[expose, reducible] def fiber {m : ℕ} : Tree m → HilbertDatum :=
  Tree.rec leafDatum (fun _ children => HilbertDatum.finiteTensor m children)
@[expose] abbrev Space (m : ℕ) := lp (fun t : Tree m => (fiber t).Carrier) 2
/-- Root-tuple completed tensor summands: the canonical distributed tensor-domain. -/
@[expose] abbrev RootTensorSpace (m : ℕ) :=
  lp (fun ts : Fin m → Tree m => (fiber (Tree.graft ts)).Carrier) 2
@[expose] def mask {m : ℕ} (s : Set (Tree m)) (v : Space m) : Space m :=
  ⟨fun t => if t ∈ s then v t else 0,
    (lp.memℓp v).mono' (fun t => by split_ifs <;> simp)⟩
@[expose] def heightProjection {m : ℕ} (j : ℕ) : Space m → Space m := mask {t | t.height = j}
@[simp] theorem heightProjection_apply {m : ℕ} (j : ℕ) (v : Space m) (t : Tree m) :
    heightProjection j v t = if t.height = j then v t else 0 := by
  simp [heightProjection, mask]
theorem norm_sq_eq_tsum {m : ℕ} (v : Space m) :
    ‖v‖ ^ 2 = ∑' t, ‖v t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  simp only [real_inner_self_eq_norm_sq]
theorem summable_norm_sq {m : ℕ} (v : Space m) :
    Summable (fun t => ‖v t‖ ^ 2) := by
  simpa only [real_inner_self_eq_norm_sq] using lp.summable_inner (𝕜 := ℝ) v v
/-- Ordered root grafting, extended by zero in the one-leaf summand. -/
@[expose] def graft {m : ℕ} (w : RootTensorSpace m) : Space m := by
  let f : (t : Tree m) → (fiber t).Carrier :=
    fun t => match t with | .leaf => 0 | .graft ts => w ts
  refine ⟨f, memℓp_gen ?_⟩
  apply Tree.graft_injective.summable_iff (f := fun t => ‖f t‖ ^ (2 : ℝ≥0∞).toReal) ?_ |>.mp
  · simpa [f, Function.comp_def] using (lp.memℓp w).summable (by norm_num)
  · intro t ht
    cases t with
    | leaf => simp [f]
    | graft ts => exact False.elim (ht ⟨ts, rfl⟩)
@[expose] def heightMass {m : ℕ} (v : Space m) (j : ℕ) : ℝ := ‖heightProjection j v‖ ^ 2
theorem hasSum_heightMass {m : ℕ} (v : Space m) : HasSum (heightMass v) (‖v‖ ^ 2) := by
  have hs := (summable_norm_sq v).hasSum.tsum_fiberwise Tree.height
  rw [← norm_sq_eq_tsum] at hs
  convert hs using 1
  funext j
  rw [heightMass, norm_sq_eq_tsum]
  rw [tsum_subtype (Tree.height ⁻¹' {j}) (fun t : Tree m => ‖v t‖ ^ 2)]
  apply tsum_congr
  intro t
  simp only [heightProjection_apply, Set.indicator]
  split_ifs <;> simp_all
end SphericalAging.CausalTree
