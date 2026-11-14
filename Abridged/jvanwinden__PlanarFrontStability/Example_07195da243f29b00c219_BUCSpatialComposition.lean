module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Lattice

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.vef976335a54d.Planarwave.Analysis.BUC ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
@[expose] public section
/-!
# Bounded uniformly continuous functions

This file bundles bounded uniformly continuous functions.  The norm and metric are inherited from
`BoundedContinuousFunction`, so the norm is the supremum norm.  In particular, this is a Banach
space whenever the codomain is a Banach space.

The basic pre- and postcomposition operations below are intended to support convolution operators
and, in particular, the heat semigroup on Euclidean space.
-/
open Bornology Filter Function Set Topology
open scoped BoundedContinuousFunction Topology
universe u v w
noncomputable section
/-- A bounded uniformly continuous function from `α` to `E`.

The bounded continuous function is stored explicitly so that the supremum norm and the existing
`BoundedContinuousFunction` API can be reused. -/
structure BUC (α : Type u) (E : Type v) [UniformSpace α] [PseudoMetricSpace E] where
  /-- The underlying bounded continuous function. -/
  toBCF : α →ᵇ E
  /-- The underlying function is uniformly continuous. -/
  uniformContinuous' : UniformContinuous (toBCF : α → E)
namespace BUC
variable {α : Type u} {β : Type v} {E : Type w}
section Basic
variable [UniformSpace α] [PseudoMetricSpace E]
instance instFunLike : FunLike (BUC α E) α E where
  coe f := f.toBCF
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact BoundedContinuousFunction.ext fun x ↦ congr_fun h x
/-- Reinterpret a bounded uniformly continuous function as a bounded continuous function. -/
instance instCoeBCF : Coe (BUC α E) (α →ᵇ E) := ⟨toBCF⟩

@[ext]
axiom ext {f g : BUC α E} (h : ∀ x, f x = g x) : f = g
axiom toBCF_injective : Injective (toBCF : BUC α E → α →ᵇ E)
/-- A bounded uniformly continuous function is uniformly continuous. -/
protected axiom uniformContinuous (f : BUC α E) : UniformContinuous (f : α → E)

/-- Precomposition by a uniformly continuous function. -/
def comp {β : Type v} [UniformSpace β] (f : BUC α E) (g : β → α)
    (hg : UniformContinuous g) : BUC β E where
  toBCF := f.toBCF.compContinuous ⟨g, hg.continuous⟩
  uniformContinuous' := f.uniformContinuous.comp hg

end Basic
section Algebra
variable [UniformSpace α] [NormedAddCommGroup E]
instance instZero : Zero (BUC α E) := ⟨⟨0, uniformContinuous_const⟩⟩
@[simp]
axiom coe_zero : ⇑(0 : BUC α E) = 0

instance instAdd : Add (BUC α E) :=
  ⟨fun f g ↦ ⟨f.toBCF + g.toBCF, f.uniformContinuous.add g.uniformContinuous⟩⟩
@[simp]
axiom coe_add (f g : BUC α E) : ⇑(f + g) = f + g

instance instSMulNat : SMul ℕ (BUC α E) where
  smul n f := nsmulRec n f
set_option linter.unusedVariables false in
axiom _root_.BUC.coe_nsmul.{w_u,w_w} : ∀ {α : Type w_u} {E : Type w_w} [inst : UniformSpace α] [inst_1 : NormedAddCommGroup E]
  (f : BUC α E) (n : ℕ), (⇑(n • f) : α → E) = n • (⇑f : α → E)
instance instNeg : Neg (BUC α E) := ⟨fun f ↦ ⟨-f.toBCF, f.uniformContinuous.neg⟩⟩
@[simp]
axiom coe_neg (f : BUC α E) : ⇑(-f) = -f

instance instSub : Sub (BUC α E) :=
  ⟨fun f g ↦ ⟨f.toBCF - g.toBCF, f.uniformContinuous.sub g.uniformContinuous⟩⟩
@[simp]
axiom coe_sub (f g : BUC α E) : ⇑(f - g) = f - g

instance instSMulInt : SMul ℤ (BUC α E) where
  smul z f := zsmulRec (· • ·) z f
@[simp]
axiom coe_zsmul (z : ℤ) (f : BUC α E) : ⇑(z • f) = z • ⇑f
instance instAddCommGroup : AddCommGroup (BUC α E) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun f n ↦ coe_nsmul f n) fun _ _ ↦ coe_zsmul _ _
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
instance instSMul : SMul 𝕜 (BUC α E) :=
  ⟨fun c f ↦ ⟨c • f.toBCF, f.uniformContinuous.const_smul c⟩⟩
@[simp]
axiom coe_smul (c : 𝕜) (f : BUC α E) : ⇑(c • f) = c • ⇑f

instance instModule : Module 𝕜 (BUC α E) := fast_instance%
  Function.Injective.module 𝕜
    ⟨⟨(⇑), coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul
end Algebra
section PseudoMetric
variable [UniformSpace α] [PseudoMetricSpace E]
/-- The uniform metric inherited from bounded continuous functions. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (BUC α E) :=
  PseudoMetricSpace.induced toBCF inferInstance

end PseudoMetric
section Metric
variable [UniformSpace α] [MetricSpace E]
/-- The uniform metric is a genuine metric when the codomain metric is. -/
noncomputable instance instMetricSpace : MetricSpace (BUC α E) :=
  MetricSpace.induced toBCF toBCF_injective inferInstance

end Metric
section Norm
variable [UniformSpace α] [NormedAddCommGroup E]
/-- The supremum norm inherited from bounded continuous functions. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (BUC α E) := fast_instance%
  NormedAddCommGroup.induced _ _
    (⟨⟨toBCF, rfl⟩, fun _ _ ↦ rfl⟩ : BUC α E →+ α →ᵇ E) toBCF_injective

/-- Point evaluation is bounded by the supremum norm. -/
axiom norm_apply_le (f : BUC α E) (x : α) : ‖f x‖ ≤ ‖f‖

/-- Precomposition does not increase the supremum norm. -/
axiom norm_comp_le {β : Type v} [UniformSpace β] (f : BUC α E) (g : β → α)
    (hg : UniformContinuous g) : ‖f.comp g hg‖ ≤ ‖f‖
variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

end Norm
section Postcomp
variable [UniformSpace α]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
/-- Postcomposition by a continuous linear map. -/
noncomputable def postcompCLM (L : E →L[𝕜] F) : BUC α E →L[𝕜] BUC α F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦
        ⟨L.compLeftContinuousBounded α f.toBCF, L.uniformContinuous.comp f.uniformContinuous⟩
      map_add' := fun f g ↦ by
        ext x
        change L (f x + g x) = L (f x) + L (g x)
        exact L.map_add _ _
      map_smul' := fun c f ↦ by
        ext x
        change L (c • f x) = c • L (f x)
        exact L.map_smul _ _ }
    ‖L‖ fun f ↦ by
      change ‖L.compLeftContinuousBounded α f.toBCF‖ ≤ ‖L‖ * ‖f.toBCF‖
      apply BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2
      intro x
      exact L.le_opNorm_of_le (f.norm_apply_le x)

end Postcomp
section Translate
variable [NormedAddCommGroup α] [NormedAddCommGroup E]

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

end Translate
end BUC

end
end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.vef976335a54d.Planarwave.Analysis.BUCSpatialBounds ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# Common bounds for genuine spatial derivative fields

The maximum of derivative norms through order `k` is represented by its
upper-bound predicate. This avoids choosing derivative fields before their
existence is proved. Product rules cost at most `2^k`; a regular trajectory
has a continuous, least such upper bound, suitable for integral Grönwall.
-/
open Set
namespace Planarwave
noncomputable section
universe u v w
variable {E : Type} {F : Type u} {G : Type v} {H : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
/-- Every genuine BUC derivative through order `k` has norm at most `A`. -/
def BUCSpatialBound : (k : ℕ) → {F : Type u} →
    [NormedAddCommGroup F] → [NormedSpace ℝ F] → BUC E F → ℝ → Prop
  | 0, _, _, _, f, A => ‖f‖ ≤ A
  | k + 1, F, _, _, f, A => ‖f‖ ≤ A ∧
      ∃ f' : BUC E (E →L[ℝ] F), BUCSpatialBound k f' A ∧
        ∀ x, HasFDerivAt f (f' x) x
namespace BUCSpatialBound

axiom nonneg {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A) : 0 ≤ A
axiom mono {k : ℕ} {f : BUC E F} {A B : ℝ} (hf : BUCSpatialBound k f A) (hAB : A ≤ B) :
    BUCSpatialBound k f B

end BUCSpatialBound
end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Examples.Example_07195da243f29b00c219_BUCSpatialComposition ====
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# Quantitative spatial chain rules on BUC

Repeated chain and product rules transfer common bounds on genuine BUC
derivatives through a uniformly continuous change of coordinates. The
coordinate map itself need not be bounded; only its derivatives are.
This is important for the modulation shear in Step 4 of `lem:key`.
-/
namespace Planarwave
noncomputable section
universe u v
variable {X E : Type} {F : Type u} {G : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace BUCSpatialBound
axiom postcomp {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A)
    (L : F →L[ℝ] G) : BUCSpatialBound k (BUC.postcompCLM L f) (‖L‖ * A)
/-- Pullback by a contractive linear coordinate projection preserves the common bound. -/
theorem precomp_contraction {k : ℕ} {f : BUC E F} {A : ℝ}
    (hf : BUCSpatialBound k f A) (L : X →L[ℝ] E) (hL : ‖L‖ ≤ 1) :
    BUCSpatialBound k (f.comp L L.uniformContinuous) A := by
  have hA := hf.nonneg
  induction k generalizing F with
  | zero => exact (BUC.norm_comp_le f L L.uniformContinuous).trans hf
  | succ k ih =>
    obtain ⟨hn, q, hq, hd⟩ := hf
    let _ : NormedAddCommGroup (X →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (X →L[ℝ] F) := inferInstance
    let _ : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
    let J := (ContinuousLinearMap.compL ℝ X E F).flip L
    have hJ : ‖J‖ ≤ 1 := by
      calc
        _ ≤ ‖(ContinuousLinearMap.compL ℝ X E F).flip‖ * ‖L‖ :=
          ((ContinuousLinearMap.compL ℝ X E F).flip).le_opNorm L
        _ ≤ 1 * 1 := by
          gcongr
          rw [ContinuousLinearMap.opNorm_flip]
          exact ContinuousLinearMap.norm_compL_le ℝ X E F
        _ = _ := one_mul _
    refine ⟨(BUC.norm_comp_le f L L.uniformContinuous).trans hn,
      BUC.postcompCLM J (q.comp L L.uniformContinuous),
      ((ih hq).postcomp J).mono (by nlinarith), ?_⟩
    intro x
    exact (hd (L x)).comp x L.hasFDerivAt
end BUCSpatialBound

end
end Planarwave
