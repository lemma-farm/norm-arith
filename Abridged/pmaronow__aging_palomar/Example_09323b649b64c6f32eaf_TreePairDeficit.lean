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
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

-- ==== Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.CausalTree ====
public section
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

@[expose] def mask {m : ℕ} (s : Set (Tree m)) (v : Space m) : Space m :=
  ⟨fun t => if t ∈ s then v t else 0,
    (lp.memℓp v).mono' (fun t => by split_ifs <;> simp)⟩
@[expose] def heightProjection {m : ℕ} (j : ℕ) : Space m → Space m := mask {t | t.height = j}

@[expose] def heightMass {m : ℕ} (v : Space m) (j : ℕ) : ℝ := ‖heightProjection j v‖ ^ 2

end SphericalAging.CausalTree

end
end
end

-- ==== Examples.pmaronow__aging_palomar.Examples.Example_09323b649b64c6f32eaf_TreePairDeficit ====
set_option autoImplicit false
public section
/-! Actual cross-height masses and the coherent-root pair deficit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace TensorProduct Topology
open Set Filter
namespace SphericalAging.TreePairDeficit
open CausalTree CausalTree.HilbertDatum   

local instance (α : Type) : DecidableEq α := Classical.decEq α
@[expose] def crossMass (v w : Space 2) (j : ℕ) : ℝ := inner ℝ (heightProjection j v) (heightProjection j w)
set_option linter.unusedVariables false in
theorem crossMass_summable (v w : Space 2) 
    (h_SphericalAging_CausalTree_hasSum_heightMass : ∀ {m : ℕ} (v : ↥(SphericalAging.CausalTree.Space m)),
      HasSum (SphericalAging.CausalTree.heightMass v) (‖v‖ ^ 2))
    : Summable (crossMass v w) := by
  have hs := ((h_SphericalAging_CausalTree_hasSum_heightMass v).summable.add (h_SphericalAging_CausalTree_hasSum_heightMass w).summable).mul_left (1/2:ℝ)
  apply hs.of_norm_bounded
  intro j
  change |inner ℝ (heightProjection j v) (heightProjection j w)|≤_
  have hi := abs_real_inner_le_norm (heightProjection j v) (heightProjection j w)
  dsimp only [heightMass]
  nlinarith [sq_nonneg (‖heightProjection j v‖-‖heightProjection j w‖)]
end SphericalAging.TreePairDeficit
