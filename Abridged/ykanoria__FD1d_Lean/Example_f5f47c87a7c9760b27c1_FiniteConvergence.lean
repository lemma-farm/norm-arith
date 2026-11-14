import Mathlib

-- ==== Examples.ykanoria__FD1d_Lean.Dependencies.v3d0ef8d60dc3.FD1D.Basic ====
section
/-!
# Fully dynamic matching on the line

Common definitions for the formal proof of the hierarchical quantile matching
bound.  All analytic quantities are represented in `ℝ`; finite probability
laws are represented by weighted sums over finite types.
-/
namespace FD1D
noncomputable section

/-- A probability mass function on a finite type, represented without quotienting. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

end FiniteLaw
end
end FD1D

end

-- ==== Examples.ykanoria__FD1d_Lean.Dependencies.v3d0ef8d60dc3.FD1D.Markov ====
section
namespace FD1D
noncomputable section
/-!
# Finite inventory Markov chains

This file uses elementary finite sums throughout.  A `FiniteKernel` is a
row-stochastic matrix, and `FiniteLaw.step` is left multiplication by that
matrix.  The inventory chain near the end of the file removes one item and
then adds an independent uniformly distributed item.
-/
open scoped BigOperators Topology
open Filter Matrix
/-! ## Finite laws and stochastic kernels -/
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

end FiniteLaw
/-- A stochastic kernel on a finite state space. -/
structure FiniteKernel (α : Type*) [Fintype α] where
  trans : α → α → ℝ
  trans_nonneg : ∀ x y, 0 ≤ trans x y
  sum_trans : ∀ x, ∑ y, trans x y = 1
namespace FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
instance : CoeFun (FiniteKernel α) fun _ => α → α → ℝ :=
  ⟨FiniteKernel.trans⟩
/-- The row-stochastic matrix of a finite kernel. -/
def matrix (K : FiniteKernel α) : Matrix α α ℝ := K.trans

/-- Advance a law by one step of the kernel. -/
def step (K : FiniteKernel α) (μ : FiniteLaw α) : FiniteLaw α where
  mass y := ∑ x, μ.mass x * K x y
  mass_nonneg y :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.mass_nonneg x) (K.trans_nonneg x y)
  sum_mass := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, K.sum_trans, mul_one]
    exact μ.sum_mass

/-- The law after `n` steps. -/
def iterate (K : FiniteKernel α) : ℕ → FiniteLaw α → FiniteLaw α
  | 0, μ => μ
  | n + 1, μ => K.step (K.iterate n μ)

/-- The `n`-step transition probability. -/
def pow [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x y : α) : ℝ :=
  (K.matrix ^ n) x y

set_option linter.unusedVariables false in
axiom _root_.FD1D.FiniteKernel.pow_nonneg.{w_u_1} : ∀ {α : Type w_u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (K : FD1D.FiniteKernel α) (n : ℕ)
  (x y : α), 0 ≤ K.pow n x y
set_option linter.unusedVariables false in
axiom _root_.FD1D.FiniteKernel.sum_pow.{w_u_1} : ∀ {α : Type w_u_1} [inst : Fintype α] [inst_1 : DecidableEq α] (K : FD1D.FiniteKernel α) (n : ℕ)
  (x : α), ∑ y : α, K.pow n x y = 1

/-! ### Existence of a stationary law -/

/-! ## Equivariance and invariant laws -/

end FiniteKernel
/-! ## Inventory vectors and delete/arrive dynamics -/

namespace InventoryState
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end InventoryState

namespace DeletionRule
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

end DeletionRule
end
end FD1D

end

-- ==== Examples.ykanoria__FD1d_Lean.Examples.Example_f5f47c87a7c9760b27c1_FiniteConvergence ====
namespace FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
namespace FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The `ℓ¹` distance between two finite probability laws. -/
def lawL1 (μ ν : FiniteLaw α) : ℝ :=
  ∑ x, |μ.mass x - ν.mass x|


set_option linter.unusedVariables false in
private theorem lawL1_iterate_le
    (K : FiniteKernel α) (n : ℕ) (μ ν : FiniteLaw α) 
    (h_FD1D_FiniteKernel_mass_iterate_sub : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] [Nonempty α] (K : FD1D.FiniteKernel α)
      (n : ℕ) (μ ν : FD1D.FiniteLaw α) (y : α),
      (K.iterate n μ).mass y - (K.iterate n ν).mass y = ∑ x : α, (μ.mass x - ν.mass x) * K.pow n x y)
    :
    lawL1 (K.iterate n μ) (K.iterate n ν) ≤ lawL1 μ ν := by
  unfold lawL1
  simp_rw [h_FD1D_FiniteKernel_mass_iterate_sub]
  calc
    (∑ y, |∑ x, (μ.mass x - ν.mass x) * K.pow n x y|) ≤
        ∑ y, ∑ x, |(μ.mass x - ν.mass x) * K.pow n x y| := by
      exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ∑ y, |μ.mass x - ν.mass x| * K.pow n x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (K.pow_nonneg n x y)]
    _ = ∑ x, |μ.mass x - ν.mass x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, K.sum_pow, mul_one]

end FiniteKernel
end
end FD1D
