module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v8bd3b45e6f34.FroehlichSpencer.Infra.Green.Basic ====
public section
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite-volume restrictions of a kernel plus a potential

Generic setting for infinite-volume Green functions: an index type `X`, a kernel
`a : X → X → ℂ` (the "hopping" part) and a real potential `v : X → ℝ`.

For a finite set
`Λ : Finset X`, `restrictedOp a v Λ` is the matrix `a|_Λ + diagonal v|_Λ` on the subtype `Λ`, and
`resolventColumn a v Λ z y` is the column `y` of `(restrictedOp a v Λ - z • 1)⁻¹`, extended by
zero outside `Λ`.

Motivation: the finite-volume Hamiltonians `H_Λ` and Green functions `G_Λ` of
Fröhlich–Spencer (1983), (1.9), (1.28)–(1.29), Fröhlich–Spencer (1983); no lattice or
Laplacian is defined here.
-/
@[expose] public section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X]
/-- The matrix `a|_Λ + diagonal v|_Λ` on the finite set `Λ`. -/
noncomputable def restrictedOp (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) : Matrix Λ Λ ℂ :=
  Matrix.of (fun x y : Λ => a x y) + Matrix.diagonal (fun x : Λ => (v x : ℂ))

end FroehlichSpencer.Infra

end
end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_99fa8e82a957a414779e_PathExpansion ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Diagonal-dominance decay of finite-volume resolvents

If `|v x - z| ≥ N > K` on a finite volume `Λ`, where `K` bounds the row sums of the kernel `a`,
then `restrictedOp a v Λ - z • 1` is invertible and the resolvent column decays like
`(K / N) ^ ⌈d x y⌉₊ / (N - K)`, for every complex `z`.

The proof is by maximum propagation, with no
Neumann series.

Motivation: the base-scale mechanism of Fröhlich–Spencer (1983), Appendix A,
Fröhlich–Spencer (1983).
-/
@[expose] public section
open Matrix
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}


set_option linter.unusedVariables false in
theorem isUnit_restrictedOp_sub_of_diag_dominant (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) (Λ : Finset X) {z : ℂ} {N : ℝ} (hKN : K < N)
    (hv : ∀ x ∈ Λ, N ≤ ‖(v x : ℂ) - z‖) 
    (h_FroehlichSpencer_Infra_restrictedOp_sub_smul_mulVec_apply : ∀ {X : Type u_1} [inst : DecidableEq X] {a : X → X → ℂ} (v : X → ℝ) (Λ : Finset X) (z : ℂ)
      (u : X → ℂ) (x : ↥Λ),
      (FroehlichSpencer.Infra.restrictedOp a v Λ - z • 1).mulVec (fun (w : ↥Λ) ↦ u (↑w : X)) x =
        ((↑(v (↑x : X)) : ℂ) - z) * u (↑x : X) + ∑ w ∈ Λ, a (↑x : X) w * u w)
    (h_FroehlichSpencer_Infra_norm_mul_le_of_row : ∀ {X : Type u_1} {a : X → X → ℂ} {K : ℝ},
      (∀ (x : X) (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K) →
        ∀ (v : X → ℝ) (Λ : Finset X) {z : ℂ} {N : ℝ},
          (∀ x ∈ Λ, N ≤ ‖(↑(v x) : ℂ) - z‖) →
            ∀ {g r : X → ℂ} {x : X},
              x ∈ Λ →
                ((↑(v x) : ℂ) - z) * g x + ∑ w ∈ Λ, a x w * g w = r x →
                  ∀ {R B : ℝ},
                    ‖r x‖ ≤ R → 0 ≤ B → (∀ w ∈ Λ, a x w ≠ 0 → ‖g w‖ ≤ B) → N * ‖g x‖ ≤ R + K * B)
    :
    IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) := by
  set M := restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ) with hM
  rw [← Matrix.mulVec_injective_iff_isUnit]
  refine (injective_iff_map_eq_zero M.mulVecLin).2 fun u hu => ?_
  have hu : M *ᵥ u = 0 := hu
  by_contra hne
  obtain ⟨x0, h0⟩ := Function.ne_iff.1 hne
  let f : X → ℂ := fun w => if h : w ∈ Λ then u ⟨w, h⟩ else 0
  have hf : ∀ w : Λ, f w = u w := fun w => by simp [f, w.2]
  obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image Λ (fun w => ‖f w‖) ⟨x0, x0.2⟩
  have hrow := h_FroehlichSpencer_Infra_restrictedOp_sub_smul_mulVec_apply (a := a) v Λ z f ⟨xs, hxs⟩
  have hfu : (fun w : Λ => f w) = u := funext hf
  rw [hfu, hu] at hrow
  have := h_FroehlichSpencer_Infra_norm_mul_le_of_row hK v Λ hv (g := f) (r := fun _ => 0) hxs
    (by simpa using hrow.symm) (R := 0) (B := ‖f xs‖) (by simp) (norm_nonneg _)
    (fun w hw _ => hmax w hw)
  have hxs0 : ‖f xs‖ = 0 := by
    have : (N - K) * ‖f xs‖ ≤ 0 := by linarith
    nlinarith [norm_nonneg (f xs)]
  have hall : ∀ w : Λ, u w = 0 := fun w => by
    have := hmax w w.2
    rw [hxs0, hf] at this
    exact norm_le_zero_iff.1 this
  exact h0 (hall x0)

end FroehlichSpencer.Infra
