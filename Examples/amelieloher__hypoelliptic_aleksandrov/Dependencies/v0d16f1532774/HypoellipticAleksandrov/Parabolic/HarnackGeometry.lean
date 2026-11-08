module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.HypoellipticAleksandrov.Parabolic.Geometry
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate geometry for the parabolic Harnack argument

The Krylov--Safonov boxes in this file use coordinate cubes.  In particular,
they are not the metric balls inherited by `PDE.Vec d`.
-/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace HypoellipticAleksandrov.Parabolic
noncomputable section
/-- The open coordinate cube of radius `r` about `v₀`. -/
def velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| < r}
/-- The closed coordinate cube of radius `r` about `v₀`. -/
def velocityClosedCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| ≤ r}
def parabolicClosedBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Icc t₀ (t₀ + vartheta * r ^ 2) ×ˢ velocityClosedCube v₀ r
@[simp] theorem mem_parabolicClosedBox_iff {d : ℕ} {vartheta r t₀ t : ℝ}
    {v₀ v : PDE.Vec d} :
    (t, v) ∈ parabolicClosedBox vartheta r t₀ v₀ ↔
      t₀ ≤ t ∧ t ≤ t₀ + vartheta * r ^ 2 ∧ v ∈ velocityClosedCube v₀ r := by
  constructor
  · rintro ⟨⟨ht₀, ht⟩, hv⟩
    exact ⟨ht₀, ht, hv⟩
  · rintro ⟨ht₀, ht, hv⟩
    exact ⟨⟨ht₀, ht⟩, hv⟩
end
end HypoellipticAleksandrov.Parabolic
