module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset

-- ==== Examples.igor_kortchemski__total_variation_threshold_parking_functions.Examples.Example_ffc3a1de81be23ac9906_Symmetrization ====
/-
Copyright (c) 2026 Igor Kortchemski.
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
set_option autoImplicit false
/-!
# The Marcinkiewicz–Zygmund inequality with exponent one, by symmetrization

The only project import is `Parking.Khintchine`, which depends on Mathlib only.

Let `α` be a finite type, `M : α → ℝ` a probability weight and `u : α → ℝ` centred under `M`:
`M ≥ 0`, `∑ a, M a = 1` and `∑ a, M a * u a = 0`. For `x : Fin k → α` put
`W x = ∏ r, M (x r)`, the law of `k` independent coordinates of law `M`, and `U_r = u (x r)`.
The main result is the Marcinkiewicz–Zygmund inequality with exponent one
(`marcinkiewiczZygmund_one`):

$$
\frac1{2\sqrt3}\,\mathbb E\Bigl(\sum_rU_r^2\Bigr)^{1/2}\le\mathbb E\Bigl\lvert\sum_rU_r\Bigr\rvert
\le2\,\mathbb E\Bigl(\sum_rU_r^2\Bigr)^{1/2}.
$$

The proof uses symmetrization with an
independent copy `y : Fin k → α` of `x`:

* (J) *Jensen in the copy* (`abs_sum_mul_le_sum_prod_mul_abs`): for all coefficients `c`,
  `|∑ r, c_r U_r| ≤ 𝔼_y |∑ r, c_r (U_r - U'_r)|`. It uses only the centring of `u`
  (`sum_prod_mul_eq_zero`) and the triangle inequality.
* (W) *Swap* (`sum_sum_prod_mul_abs_sum_ite_neg`): for every sign pattern `ε`, exchanging
  `x r` and `y r` for the coordinates `r` with a negative sign is an involution of
  `(Fin k → α) × (Fin k → α)` that preserves the weight `W x W y`, so the signed differences
  `∑ r, ε_r (U_r - U'_r)` and the plain differences `∑ r, (U_r - U'_r)` have the same
  absolute first moment.
* Khintchine's inequality (`khintchine_one`) is applied pointwise, and the upper bound ends
  with the triangle inequality in `ℓ²` (`sqrt_sum_sub_sq_le`).
-/
public section
namespace Parking
open Finset
/-! ### Product weights -/

/-! ### Jensen in the independent copy -/
set_option linter.unusedVariables false in
/-- **Jensen in the independent copy** (lemma (J)). For a centred `u` and arbitrary
coefficients `c`, `|∑ r, c_r u (x r)| ≤ ∑ y, (∏ r, M (y r)) |∑ r, c_r (u (x r) - u (y r))|`.
Symmetry of `u` is not needed. -/
theorem abs_sum_mul_le_sum_prod_mul_abs {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) {k : ℕ}
    (c : Fin k → ℝ) (x : Fin k → α) 
    (h_Parking_sum_prod_mul_eq_zero : ∀ {α : Type u_1} [inst : Fintype α] (M u : α → ℝ),
      ∑ a : α, M a * u a = 0 →
        ∀ {k : ℕ} (r : Fin k), ∑ y : Fin k → α, (∏ r' : Fin k, M (y r')) * u (y r) = 0)
    (h_Parking_sum_prod_eq_one : ∀ {α : Type u_1} [inst : Fintype α] (M : α → ℝ),
      ∑ a : α, M a = 1 → ∀ (k : ℕ), ∑ x : Fin k → α, ∏ r : Fin k, M (x r) = 1)
    :
    |∑ r, c r * u (x r)| ≤
      ∑ y : Fin k → α, (∏ r, M (y r)) * |∑ r, c r * (u (x r) - u (y r))| := by
  have hW : ∀ y : Fin k → α, 0 ≤ ∏ r, M (y r) := fun y => Finset.prod_nonneg fun r _ => hM _
  have hmean : ∑ y : Fin k → α, (∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r)) =
      ∑ r, c r * u (x r) := by
    calc ∑ y : Fin k → α, (∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r))
        = ∑ y : Fin k → α, ((∏ r, M (y r)) * ∑ r, c r * u (x r) -
            ∑ r, c r * ((∏ r', M (y r')) * u (y r))) :=
          Finset.sum_congr rfl fun y _ => by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun r _ => by ring
      _ = (∑ y : Fin k → α, ∏ r, M (y r)) * ∑ r, c r * u (x r) -
            ∑ r, c r * ∑ y : Fin k → α, (∏ r', M (y r')) * u (y r) := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = ∑ r, c r * u (x r) := by
          simp only [h_Parking_sum_prod_eq_one M hM1, h_Parking_sum_prod_mul_eq_zero M u hu, mul_zero,
            Finset.sum_const_zero, one_mul, sub_zero]
  calc |∑ r, c r * u (x r)|
      = |∑ y : Fin k → α, (∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r))| := by rw [hmean]
    _ ≤ ∑ y : Fin k → α, |(∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y : Fin k → α, (∏ r, M (y r)) * |∑ r, c r * (u (x r) - u (y r))| :=
        Finset.sum_congr rfl fun y _ => by rw [abs_mul, abs_of_nonneg (hW y)]

/-! ### The swap involution -/

/-! ### The triangle inequality in `ℓ²` -/

/-! ### The Marcinkiewicz–Zygmund inequality -/

end Parking
