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

/-- A law is stationary when one step leaves it unchanged. -/
def IsStationary (K : FiniteKernel α) (μ : FiniteLaw α) : Prop :=
  K.step μ = μ

/-! ### Existence of a stationary law -/

/-- Reachability by a positive-probability path. -/
def Reaches [DecidableEq α] (K : FiniteKernel α) (x y : α) : Prop :=
  ∃ n : ℕ, 0 < K.pow n x y
/-- Every state can be reached from every other state. -/
def Irreducible [DecidableEq α] (K : FiniteKernel α) : Prop :=
  ∀ x y, K.Reaches x y

/-- Strictly positive one-step self-loops. -/
def HasPositiveLoops (K : FiniteKernel α) : Prop :=
  ∀ x, 0 < K x x
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

-- ==== Examples.ykanoria__FD1d_Lean.Examples.Example_fd077c94efbb0f136980_FiniteConvergence ====
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
private theorem tendsto_lawL1_zero
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) 
    (h_FD1D_FiniteKernel_exists_pow_pos : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] [Nonempty α] (K : FD1D.FiniteKernel α),
      K.Irreducible → K.HasPositiveLoops → ∃ (N : ℕ), 0 < N ∧ ∀ (x y : α), 0 < K.pow N x y)
    (h_FD1D_FiniteKernel_lawL1_iterate_geometric : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] [Nonempty α] (K : FD1D.FiniteKernel α)
      (π μ : FD1D.FiniteLaw α),
      K.IsStationary π →
        ∀ (N : ℕ),
          0 < N →
            ∀ (ε : ℝ),
              (∀ (x y : α), ε ≤ K.pow N x y) →
                (↑(Fintype.card α) : ℝ) * ε ≤ 1 →
                  ∀ (n : ℕ),
                    FD1D.FiniteKernel.lawL1 (K.iterate n μ) π ≤
                      (1 - (↑(Fintype.card α) : ℝ) * ε) ^ (n / N) * FD1D.FiniteKernel.lawL1 μ π)
    (h_FD1D_FiniteKernel_lawL1_nonneg : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α] [Nonempty α] (μ ν : FD1D.FiniteLaw α),
      0 ≤ FD1D.FiniteKernel.lawL1 μ ν)
    (h_FD1D_FiniteKernel_exists_minorization : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] [Nonempty α] (K : FD1D.FiniteKernel α)
      {N : ℕ},
      (∀ (x y : α), 0 < K.pow N x y) →
        ∃ (ε : ℝ), 0 < ε ∧ (∀ (x y : α), ε ≤ K.pow N x y) ∧ (↑(Fintype.card α) : ℝ) * ε ≤ 1)
    :
    Tendsto (fun n => lawL1 (K.iterate n μ) π) atTop (𝓝 0) := by
  obtain ⟨N, hN, hpow⟩ := h_FD1D_FiniteKernel_exists_pow_pos K hirr hloop
  obtain ⟨ε, hεpos, hε, hc⟩ := h_FD1D_FiniteKernel_exists_minorization K hpow
  let q := 1 - (Fintype.card α : ℝ) * ε
  have hq0 : 0 ≤ q := sub_nonneg.mpr hc
  have hcard : 0 < (Fintype.card α : ℝ) := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hpowlim :
      Tendsto (fun n : ℕ => q ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (Nat.tendsto_div_const_atTop hN.ne')
  refine squeeze_zero (fun n => h_FD1D_FiniteKernel_lawL1_nonneg (K.iterate n μ) π)
    (fun n => h_FD1D_FiniteKernel_lawL1_iterate_geometric K π μ hπ N hN ε hε hc n) ?_
  simpa [q] using hpowlim.mul_const (lawL1 μ π)

end FiniteKernel
end
end FD1D
