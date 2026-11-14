module

public import Mathlib

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v951a6a1e3944.SKConstants.Upstream.OAI.Probability.SKBarriers.Model ====
public section
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Model.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK
abbrev Config (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ
def spin (b : Bool) : ℝ := if b then 1 else -1
def hamiltonian {n : ℕ} (J : Disorder n) (x : Config n) : ℝ :=
  (∑ e : Edge n, J e * spin (x e.val.1) * spin (x e.val.2)) / Real.sqrt n
def partition {n : ℕ} (β : ℝ) (J : Disorder n) : ℝ :=
  ∑ x : Config n, Real.exp (β * hamiltonian J x)
def gibbs {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) : ℝ :=
  Real.exp (β * hamiltonian J x) / partition β J
def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)
end SK
end
end
end
end SKConstantsOAI

end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Examples.Example_c32572fb46f3b532a4b1_DisorderPairs ====
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/SpinGlass/DisorderPairs.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

def directionalEnergy {n : ℕ} (β : ℝ) (J K : Disorder n) : ℝ :=
  β * ∑ x : Config n, gibbs β J x * hamiltonian K x


set_option linter.unusedVariables false in
theorem directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) 
    (h_SKConstantsOAI_SK_directionalEnergy_exp_le : ∀ {n : ℕ} (β ℓ : ℝ) (J K : SKConstantsOAI.SK.Disorder n),
      Real.exp (ℓ * SKConstantsOAI.SK.directionalEnergy β J K) ≤
        ∑ x : SKConstantsOAI.SK.Config n,
          SKConstantsOAI.SK.gibbs β J x * Real.exp (ℓ * β * SKConstantsOAI.SK.hamiltonian K x))
    (h_SKConstantsOAI_SK_hamiltonian_gaussian : ∀ {n : ℕ} (x : SKConstantsOAI.SK.Config n),
      ProbabilityTheory.HasGaussianLaw
        (fun (J : SKConstantsOAI.SK.Disorder n) ↦ SKConstantsOAI.SK.hamiltonian J x)
        (SKConstantsOAI.SK.disorderLaw n))
    (h_SKConstantsOAI_SK_gaussian_exp_integrable : ∀ {Ω : Type} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ},
      ProbabilityTheory.HasGaussianLaw X μ →
        ∀ (t : ℝ), MeasureTheory.Integrable (fun (ω : Ω) ↦ Real.exp (t * X ω)) μ)
    (h_SKConstantsOAI_SK_gibbs_sum : ∀ {n : ℕ} (β : ℝ) (J : SKConstantsOAI.SK.Disorder n),
      ∑ x : SKConstantsOAI.SK.Config n, SKConstantsOAI.SK.gibbs β J x = 1)
    (h_SKConstantsOAI_SK_directionalEnergy_exp_integrable : ∀ {n : ℕ} (β ℓ : ℝ) (J : SKConstantsOAI.SK.Disorder n),
      MeasureTheory.Integrable
        (fun (K : SKConstantsOAI.SK.Disorder n) ↦
          Real.exp (ℓ * SKConstantsOAI.SK.directionalEnergy β J K))
        (SKConstantsOAI.SK.disorderLaw n))
    (h_SKConstantsOAI_SK_hamiltonian_exp_integral : ∀ {n : ℕ},
      0 < n →
        ∀ (x : SKConstantsOAI.SK.Config n) (t : ℝ),
          ∫ (J : SKConstantsOAI.SK.Disorder n),
              Real.exp (t * SKConstantsOAI.SK.hamiltonian J x) ∂SKConstantsOAI.SK.disorderLaw n =
            Real.exp (t ^ 2 * ((↑n : ℝ) - 1) / 4))
    :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (h_SKConstantsOAI_SK_gaussian_exp_integrable (h_SKConstantsOAI_SK_hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (h_SKConstantsOAI_SK_directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (h_SKConstantsOAI_SK_directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, h_SKConstantsOAI_SK_hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, h_SKConstantsOAI_SK_gibbs_sum, one_mul]
end SK
end
end
end
end SKConstantsOAI
