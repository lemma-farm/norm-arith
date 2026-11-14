module

public import Mathlib
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

-- ==== Examples.WozMit__hitting_time_loose_hamilton.Dependencies.v4e0e457f2bed.HittingTimeLooseHamilton.KahnEntropy ====
public section
public section
open scoped BigOperators
noncomputable section
namespace FiniteEntropy
variable {A B : Type*} [Fintype A] [Fintype B]
structure Law (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1
end FiniteEntropy

end
end
end

-- ==== Examples.WozMit__hitting_time_loose_hamilton.Dependencies.v4e0e457f2bed.HittingTimeLooseHamilton.KahnLaw ====
public section
public section
open scoped BigOperators
noncomputable section
namespace FiniteEntropy
namespace Law
variable {A B : Type*} [Fintype A] [Fintype B]
/-- Probability of an event in a finite probability space. -/
@[expose] noncomputable def event (p : Law A) (E : A → Prop) : ℝ := by
  classical
  exact ∑ a, if E a then p.mass a else 0

set_option linter.unusedVariables false in
axiom _root_.FiniteEntropy.Law.event_mono.{w_u_1} : ∀ {A : Type w_u_1} [inst : Fintype A] (p : FiniteEntropy.Law A) {E F : A → Prop},
  (∀ (a : A), E a → F a) → p.event E ≤ p.event F

end Law
end FiniteEntropy

end
end
end

-- ==== Examples.WozMit__hitting_time_loose_hamilton.Examples.Example_240453521b60f069c96b_FiniteMomentBounds ====
public section
/-! Elementary finite probability bounds and moment identities.
All sums use the existing finite-law mass function; no measure-theoretic or
independence assumptions are introduced. -/
noncomputable section
open scoped BigOperators
namespace FiniteEntropy.Law
variable {Ω I : Type*} [Fintype Ω] [Fintype I]
/-- Expectation of a real-valued function under a finite law. -/
@[expose] def finiteMean (p : FiniteEntropy.Law Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, p.mass ω * X ω

set_option linter.unusedVariables false in
axiom _root_.FiniteEntropy.Law.finite_markov.{w_u_1} : ∀ {Ω : Type w_u_1} [inst : Fintype Ω] (p : FiniteEntropy.Law Ω) {X : Ω → ℝ},
  (∀ (ω : Ω), 0 ≤ X ω) → ∀ {a : ℝ}, 0 < a → (p.event fun (ω : Ω) ↦ a ≤ X ω) ≤ p.finiteMean X / a

set_option linter.unusedVariables false in
axiom _root_.FiniteEntropy.Law.finiteMean_squared_deviation.{w_u_1} : ∀ {Ω : Type w_u_1} [inst : Fintype Ω] (p : FiniteEntropy.Law Ω) (X : Ω → ℝ),
  (p.finiteMean fun (ω : Ω) ↦ (X ω - p.finiteMean X) ^ 2) =
    (p.finiteMean fun (ω : Ω) ↦ X ω ^ 2) - p.finiteMean X ^ 2
/-- The standard second-moment upper bound for the probability of a zero count.
It actually holds for any real-valued random variable with positive mean. -/
theorem finite_second_moment_zero (p : FiniteEntropy.Law Ω) (X : Ω → ℝ)
    (hmean : 0 < p.finiteMean X) :
    p.event (fun ω => X ω = 0) ≤
      (p.finiteMean (fun ω => (X ω)^2) - (p.finiteMean X)^2) /
        (p.finiteMean X)^2 := by
  have hmono : p.event (fun ω => X ω = 0) ≤
      p.event (fun ω => (p.finiteMean X)^2 ≤ (X ω - p.finiteMean X)^2) := by
    apply p.event_mono
    intro ω hω
    simp [hω]
  have hmarkov := p.finite_markov (fun ω => sq_nonneg (X ω - p.finiteMean X)) (sq_pos_of_pos hmean)
  rw [p.finiteMean_squared_deviation X] at hmarkov
  exact hmono.trans hmarkov

end FiniteEntropy.Law
