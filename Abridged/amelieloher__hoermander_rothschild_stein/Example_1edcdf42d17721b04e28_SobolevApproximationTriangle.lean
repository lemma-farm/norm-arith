module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.Hormander.Interface.BasisVec ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Hormander.Interface
/-- The `i`-th standard basis vector of `Fin N → ℝ`. -/
def basisVec {d : ℕ} (i : Fin d) : Fin d → ℝ := Pi.single i (1 : ℝ)
end Hormander.Interface

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.Hormander.Interface.EuclideanDivergence ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Hormander.Interface
/-- The Euclidean divergence of a vector field, in the canonical coordinates. -/
def euclideanDivergence {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (fderiv ℝ V x (basisVec i)) i
end Hormander.Interface

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.fieldTranspose ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def fieldTranspose {n : ℕ} (V : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  -Hormander.Interface.euclideanDivergence (fun y => φ y • V y) x
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.wordTranspose ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def wordTranspose {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) :
    List (Fin m) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)
  | [], φ => φ
  | i :: I, φ => wordTranspose X I (fieldTranspose (X i) φ)
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.hasWeakWordDeriv ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def hasWeakWordDeriv {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (I : List (Fin m))
    (f g : (Fin n → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn f (V : Set (Fin n → ℝ)) volume ∧
  LocallyIntegrableOn g (V : Set (Fin n → ℝ)) volume ∧
  ∀ φ : TestFunction V ℝ (⊤ : ℕ∞),
    (∫ x in (V : Set (Fin n → ℝ)), g x * φ x) =
    ∫ x in (V : Set (Fin n → ℝ)), f x * wordTranspose X I φ x
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.S.WeakSub ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}
/-- Differences of weak word derivatives are derivatives of the
corresponding difference (BB Def. 2.1, pp. 67–68). -/
axiom hasWeakWordDeriv_sub
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {I : List (Fin m)} {f g h k : (Fin n → ℝ) → ℝ}
    (hf : hasWeakWordDeriv X Ω I f g) (hh : hasWeakWordDeriv X Ω I h k) :
    hasWeakWordDeriv X Ω I (fun x => f x - h x) (fun x => g x - k x)
end RothschildStein.S

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.wordWeight ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def wordWeight {m : ℕ} (w : Fin m → ℕ+) (I : List (Fin m)) : ℕ :=
  (I.map fun i => (w i : ℕ)).sum
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.wordFamily ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def wordFamily {m : ℕ} (w : Fin m → ℕ+) (k : ℕ) : Finset (List (Fin m)) := by
  classical
  exact ((Finset.range (k + 1)).biUnion fun l =>
    (Finset.univ : Finset (Fin l → Fin m)).image List.ofFn).filter
      (fun I => wordWeight w I ≤ k)
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.memSobolevX ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def memSobolevX {m n : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  MemLp f p (volume.restrict (V : Set (Fin n → ℝ))) ∧
  ∀ I ∈ wordFamily w k, ∃ g : (Fin n → ℝ) → ℝ,
    hasWeakWordDeriv X V I f g ∧
    MemLp g p (volume.restrict (V : Set (Fin n → ℝ)))
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.weakWordENorm ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def weakWordENorm {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ g : (Fin n → ℝ) → ℝ,
    hasWeakWordDeriv X V I f g ∧
    AEStronglyMeasurable g (volume.restrict (V : Set (Fin n → ℝ))) ∧
    r = eLpNorm g p (volume.restrict (V : Set (Fin n → ℝ)))}
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.Definitions.sobolevXENorm ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
def sobolevXENorm {m n : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ wordFamily w k, weakWordENorm X V I p f
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.va9b82140df54.RothschildStein.S.Sobolev ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {m n : ℕ}

/-- The infimum norm equals the norm of any weak representative
(BB Def. 2.2, p. 68; uniqueness). -/
axiom weakWordENorm_eq (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞)
    (f g : (Fin n → ℝ) → ℝ) (hg : hasWeakWordDeriv X Ω I f g) :
    weakWordENorm X Ω I p f = eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ)))

end RothschildStein.S

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_1edcdf42d17721b04e28_SobolevApproximationTriangle ====
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3
/-- The fixed Sobolev norm obeys the triangle inequality for successive
approximation errors, using uniqueness of weak word representatives. -/
theorem sobolevXENorm_sub_le_sub_add_sub {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    {u v z : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX w X Ω k p u) (hv : memSobolevX w X Ω k p v)
    (hz : memSobolevX w X Ω k p z) :
    sobolevXENorm w X Ω k p (fun x => u x-z x) ≤
      sobolevXENorm w X Ω k p (fun x => u x-v x) +
      sobolevXENorm w X Ω k p (fun x => v x-z x) := by
  classical
  unfold sobolevXENorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro I hI
  obtain ⟨a,ha,_⟩ := hu.2 I hI
  obtain ⟨b,hb,_⟩ := hv.2 I hI
  obtain ⟨c,hc,_⟩ := hz.2 I hI
  rw [S.weakWordENorm_eq X Ω I p _ _ (S.hasWeakWordDeriv_sub X Ω hX ha hc),
    S.weakWordENorm_eq X Ω I p _ _ (S.hasWeakWordDeriv_sub X Ω hX ha hb),
    S.weakWordENorm_eq X Ω I p _ _ (S.hasWeakWordDeriv_sub X Ω hX hb hc)]
  have he : (fun x => a x-c x) = (fun x => a x-b x) + (fun x => b x-c x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact eLpNorm_add_le hp
end RothschildStein.H3
