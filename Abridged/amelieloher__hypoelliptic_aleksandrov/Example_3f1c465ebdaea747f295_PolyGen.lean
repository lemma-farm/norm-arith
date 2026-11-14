module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.PDEFoundation.Ambient.Basic ====
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
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.MovingKernel ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moving-fiber kernels

This module fixes the carrier for the terminal evolution kernel.  Invalid
time pairs and off-domain source states have no values: the master kernel is
defined only on the corresponding valid-query subtype.  Fixed-time kernels
are obtained from that one master kernel by `Kernel.comap` and
`Kernel.comapRight`.
-/
@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ProbabilityTheory
namespace HypoellipticAleksandrov.KineticAleksandrov
/-- The ambient fixed-time state `(y, z)`. -/
abbrev EvolutionAmbientState (n : ℕ) := PDE.Vec n × PDE.Vec n

namespace MovingFiberKernel
end MovingFiberKernel
namespace MovingFiberKernel
end MovingFiberKernel
end HypoellipticAleksandrov.KineticAleksandrov

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Derivs ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate derivatives of the Gaussian exponential

Directional derivatives of `gaussExp a b c = exp (-quadForm a b c)` along the coordinate
directions of phase space. A direction is `δ : Fin d ⊕ Fin d`: `inl i` is the velocity direction
`e_i` and `inr i` the position direction. The Leibniz rule
`∂_δ (p * G) = (∂_δ p - p * ∂_δ Q) * G` and the constancy of the second derivatives of `Q` are
the two inputs of the polynomial calculus used for the Gaussian flow estimates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Real
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
def gen (a b c : ℝ) : Fin d ⊕ Fin d → EvolutionAmbientState d → ℝ
  | Sum.inl i, y => b * y.2 i + 2 * c * y.1 i
  | Sum.inr i, y => 2 * a * y.2 i + b * y.1 i
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.PolyClass ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomially growing coefficient families

For the Gaussian exponential `G_θ = gaussExp θ₁ θ₂ θ₃` every iterated coordinate derivative has
the form `P_θ * G_θ` where `P_θ` is a polynomial of degree at most the order. To obtain bounds
that are uniform in the coefficient triple `θ` (on bounded sets, hence on compact `h`-intervals
for the flow), we track a family `θ ↦ P_θ` in the predicate `PG k S`: degree `≤ k`, with growth
constant uniform over `Coef S = {θ | |θᵢ| ≤ S}`. This realizes the polynomial structure behind the
derivative bounds of the Gaussian flow.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
/-- The parameter triple `(a, b, c)` of the quadratic form. -/
abbrev Theta : Type := ℝ × ℝ × ℝ
/-- The coefficient triples bounded by `S`. -/
def Coef (S : ℝ) : Set Theta := {θ | |θ.1| ≤ S ∧ |θ.2.1| ≤ S ∧ |θ.2.2| ≤ S}
/-- The gradient `∂_δ Q_θ` of the quadratic form, as a function of the triple. -/
def genT (θ : Theta) (δ : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) : ℝ :=
  gen θ.1 θ.2.1 θ.2.2 δ y
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_3f1c465ebdaea747f295_PolyGen ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Iterated derivatives of the Gaussian exponential

The iterated coordinate derivatives of `K * G_θ` are polynomial multiples `K * P_θ * G_θ`, with
`P` in the class `PG` of the length of the derivative word. This is the polynomial structure behind
the derivative bounds of the Gaussian flow.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}

set_option linter.unusedVariables false in
theorem abs_genT_le {S : ℝ} {θ : Theta} (hθ : θ ∈ Coef S) (δ : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_FullCoefficient_abs_coord_le : ∀ {d : ℕ} (y : HypoellipticAleksandrov.KineticAleksandrov.EvolutionAmbientState d) (i : Fin d),
      |y.1 i| ≤ ‖y‖ ∧ |y.2 i| ≤ ‖y‖)
    : |genT θ δ y| ≤ 3 * S * (1 + ‖y‖) := by
  obtain ⟨ha, hb, hc⟩ := hθ
  have hS : 0 ≤ S := (abs_nonneg _).trans ha
  have hn := norm_nonneg y
  rcases δ with i | i
  · obtain ⟨h1, h2⟩ := h_HypoellipticAleksandrov_KineticAleksandrov_FullCoefficient_abs_coord_le y i
    unfold genT gen
    calc |θ.2.1 * y.2 i + 2 * θ.2.2 * y.1 i|
        ≤ |θ.2.1 * y.2 i| + |2 * θ.2.2 * y.1 i| := abs_add_le _ _
      _ = |θ.2.1| * |y.2 i| + 2 * |θ.2.2| * |y.1 i| := by
          rw [abs_mul, abs_mul, abs_mul]; norm_num
      _ ≤ S * ‖y‖ + 2 * S * ‖y‖ := by
          gcongr
      _ ≤ 3 * S * (1 + ‖y‖) := by nlinarith
  · obtain ⟨h1, h2⟩ := h_HypoellipticAleksandrov_KineticAleksandrov_FullCoefficient_abs_coord_le y i
    unfold genT gen
    calc |2 * θ.1 * y.2 i + θ.2.1 * y.1 i|
        ≤ |2 * θ.1 * y.2 i| + |θ.2.1 * y.1 i| := abs_add_le _ _
      _ = 2 * |θ.1| * |y.2 i| + |θ.2.1| * |y.1 i| := by
          rw [abs_mul, abs_mul, abs_mul]; norm_num
      _ ≤ 2 * S * ‖y‖ + S * ‖y‖ := by
          gcongr
      _ ≤ 3 * S * (1 + ‖y‖) := by nlinarith
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
