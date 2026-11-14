module

public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.Hormander.Interface.BasisVec ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.Hormander.Interface.EuclideanDivergence ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.holderSeminorm ====
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
def holderSeminorm {n : ℕ}
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (α : ℝ) (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {C : ℝ≥0∞ | C < ⊤ ∧
    ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ →
      ENNReal.ofReal |f x - f y| ≤ C * (d x y) ^ α}
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.holderENorm ====
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
def holderENorm {n : ℕ}
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (α : ℝ) (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  (⨆ x : V, ENNReal.ofReal |f x|) + holderSeminorm d α V f
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.DistanceGeometry ====
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
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal Topology
namespace RothschildStein.S
/-- Distance assumptions on a fixed ambient open domain:
the chosen extended metric induces the Euclidean subtype topology
(BB Def 1.38, p. 21; Thm 1.53, p. 35). This structure does not change
the ambient metric or choose a new distance after restriction. -/
structure DistanceGeometry {n : ℕ} (Ω : Opens (Fin n → ℝ)) where
  d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞
  metric : EMetricSpace Ω
  distance_eq : ∀ x y : Ω, @edist Ω metric.toEDist x y = d x.val y.val
  topology_eq : (inferInstance : TopologicalSpace Ω) = metric.toUniformSpace.toTopologicalSpace

end RothschildStein.S

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.HolderSubsetContinuity ====
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
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}
/-- Restriction retains the original ambient distance and
its Euclidean topology (BB Def 2.13, p. 81; Prop 2.18, p. 84). -/
axiom continuousOn_of_holderENorm_lt_top_subset
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    {V : Set (Fin n → ℝ)} (hV : V ⊆ Ω) {α : ℝ} (hα : 0 < α)
    {f : (Fin n → ℝ) → ℝ} (hf : holderENorm G.d α V f < ⊤) :
    ContinuousOn f V
end RothschildStein.S

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.H3.LocalHolderSupNorm ====
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
open scoped ENNReal
namespace RothschildStein.H3
/-- A local full fixed Hölder norm controls the actual
essential supremum on the same open set. Measurability is derived
from the shared ambient distance geometry and positive exponent. -/
axiom eLpNorm_top_le_local_holderNorm {N : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω) {α : ℝ} (hα : 0 < α)
    {f : (Fin N → ℝ) → ℝ}
    (hf : holderENorm G.d α (U : Set (Fin N → ℝ)) f < ⊤) :
    eLpNorm f ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤
      holderENorm G.d α (U : Set (Fin N → ℝ)) f
end RothschildStein.H3

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.fieldTranspose ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.wordTranspose ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.hasWeakWordDeriv ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.wordWeight ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.wordFamily ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.driftWeight ====
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
def driftWeight {q : ℕ} (i : Fin (q + 1)) : ℕ+ :=
  if i = 0 then 2 else 1
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.weakWordENorm ====
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

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.Sobolev ====
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

axiom weakWordENorm_eq (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞)
    (f g : (Fin n → ℝ) → ℝ) (hg : hasWeakWordDeriv X Ω I f g) :
    weakWordENorm X Ω I p f = eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ)))
/-- Deleting letters lowers weight (BB Def. 2.2, p. 68). -/
axiom wordWeight_sublist_le (w : Fin m → ℕ+) {I J : List (Fin m)}
    (h : List.Sublist I J) : wordWeight w I ≤ wordWeight w J
end RothschildStein.S

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.hasIntrinsicDeriv ====
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
def hasIntrinsicDeriv {n : ℕ} (V : Opens (Fin n → ℝ))
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (f g : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ (V : Set (Fin n → ℝ)),
    (∃ γ : ℝ → (Fin n → ℝ), γ 0 = x ∧
      IsIntegralCurveAt γ (fun _ => X) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (V : Set (Fin n → ℝ))) ∧
    ∀ γ : ℝ → (Fin n → ℝ), γ 0 = x →
      IsIntegralCurveAt γ (fun _ => X) 0 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (V : Set (Fin n → ℝ))) →
      HasDerivAt (fun t => f (γ t)) (g x) 0
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.hasIntrinsicWordDeriv ====
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
def hasIntrinsicWordDeriv {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (V : Opens (Fin n → ℝ)) :
    List (Fin m) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ) → Prop
  | [], f, g => EqOn g f (V : Set (Fin n → ℝ))
  | i :: I, f, g => ∃ h : (Fin n → ℝ) → ℝ,
      hasIntrinsicWordDeriv X V I f h ∧ hasIntrinsicDeriv V (X i) h g
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.intrinsicWordENorm ====
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
def intrinsicWordENorm {m n : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Opens (Fin n → ℝ)) (I : List (Fin m)) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ g : (Fin n → ℝ) → ℝ,
    hasIntrinsicWordDeriv X V I f g ∧
    r = holderENorm d α (V : Set (Fin n → ℝ)) g}
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.holderXENorm ====
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
def holderXENorm {m n : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ wordFamily w k, intrinsicWordENorm X d V I α f
end RothschildStein

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.H3.FirstHolderNormFormula ====
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
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

set_option linter.unusedVariables false in
axiom _root_.RothschildStein.H3.holderXENorm_drift_one_eq : ∀ {N q : ℕ} (Y : Fin (q + 1) → (Fin N → ℝ) → Fin N → ℝ) (d : (Fin N → ℝ) → (Fin N → ℝ) → ENNReal)
  (U : TopologicalSpace.Opens (Fin N → ℝ)) (α : ℝ) (u : (Fin N → ℝ) → ℝ)
  (jet : Fin q → (Fin N → ℝ) → ℝ),
  (∀ (i : Fin q), RothschildStein.hasIntrinsicWordDeriv Y U [i.succ] u (jet i)) →
    RothschildStein.holderXENorm RothschildStein.driftWeight Y d U 1 α u =
      RothschildStein.holderENorm d α (↑U : Set (Fin N → ℝ)) u +
        ∑ i : Fin q, RothschildStein.holderENorm d α (↑U : Set (Fin N → ℝ)) (jet i)
end RothschildStein.H3

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.WeakIntrinsicWords ====
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
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- Continuous weak word data provide the exact
iterated intrinsic derivative for every word. Subwords ensure
that all required suffixes are present; ordinary length drives the
induction, independently of weights (BB pp. 87–90). -/
axiom hasIntrinsicWordDeriv_of_continuous_weak_subwords
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ J,J.Sublist I → hasWeakWordDeriv X Ω J f (jet J))
    (hc : ∀ J,J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ))) :
    hasIntrinsicWordDeriv X Ω I f (jet I)
end RothschildStein.S

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_2f34683c5033d7f387de_HolderJetFirstNorm ====
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
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3
/-- The local normalized continuous weak jets control the
horizontal L infinity sum by the exact fixed full first-order norm. -/
theorem first_weakJetNorm_sum_le_holderX {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv X U I u (jet I) ∧
      holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤) :
    (∑ i : Fin q, weakWordENorm X U [i.succ] ⊤ u) ≤
      holderXENorm driftWeight X G.d U 1 α u := by
  have hi (i : Fin q) : hasIntrinsicWordDeriv X U [i.succ] u (jet [i.succ]) := by
    apply S.hasIntrinsicWordDeriv_of_continuous_weak_subwords U X hX
      [i.succ] u jet hzero
    · intro J hJ
      exact (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
        (by simp [wordWeight, driftWeight]))).1
    · intro J hJ
      exact S.continuousOn_of_holderENorm_lt_top_subset Ω G hU hα
        (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
          (by simp [wordWeight, driftWeight]))).2
  rw [holderXENorm_drift_one_eq X G.d U α u (fun i => jet [i.succ]) hi]
  apply le_trans _ (le_add_left le_rfl)
  apply Finset.sum_le_sum
  intro i _
  rw [S.weakWordENorm_eq X U [i.succ] ⊤ u (jet [i.succ])
    (hj _ (by simp [wordWeight, driftWeight])).1]
  exact eLpNorm_top_le_local_holderNorm Ω U G hU hα
    (hj _ (by simp [wordWeight, driftWeight])).2
end RothschildStein.H3
