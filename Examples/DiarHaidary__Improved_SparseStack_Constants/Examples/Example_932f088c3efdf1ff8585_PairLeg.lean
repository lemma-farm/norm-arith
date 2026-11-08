/-
Copyright (c) 2026 Diar Heidary. Released under the MIT license.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.LocalVectors
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Op.Band
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-! # Two-site local blocks, with the bucket label collected before estimating -/
open scoped BigOperators
namespace SparseStackV3.Op.PairLeg
open SparseFock SparseFock.SparseStackDistribution Occupation SiteLeg
variable {d s b n : ℕ}
noncomputable section
def factors (t1 t2 : Site s n) (A B : LocalKernel b) : Site s n → LocalKernel b :=
  fun t => if t = t1 then A else if t = t2 then B else identity
def act (hb : 0 < b) (t1 t2 : Site s n) (A B : LocalKernel b)
    (X : Vec d s b n) : Vec d s b n := tensorApply hb (factors t1 t2 A B) X
theorem act_comp (hb : 0 < b) {t1 t2 : Site s n} (ht : t1 ≠ t2)
    (A B C D : LocalKernel b) (X : Vec d s b n) :
    act hb t1 t2 A B (act hb t1 t2 C D X) =
      act hb t1 t2 (localComp hb A C) (localComp hb B D) X := by
  unfold act
  rw [tensor_comp]
  congr 1
  funext t
  by_cases h1 : t = t1
  · simp [factors, h1]
  · by_cases h2 : t = t2
    · simp only [factors, if_neg h1, if_pos h2]
    · simp [factors, h1, h2, identity_left]
theorem act_adjoint (hb : 0 < b) (t1 t2 : Site s n) (A B : LocalKernel b)
    (X Y : Vec d s b n) :
    ip hb (act hb t1 t2 A B X) Y =
      ip hb X (act hb t1 t2 (fun x y => A y x) (fun x y => B y x) Y) := by
  unfold act
  rw [tensor_adjoint]
  congr 2
  funext t x y
  by_cases h1 : t = t1
  · simp [factors, h1]
  · by_cases h2 : t = t2
    · simp only [factors, if_neg h1, if_pos h2]
    · simp [factors, h1, h2, identity_symm]
theorem level_projection_energy (hb : 0 < b) {t1 t2 : Site s n} (ht : t1 ≠ t2)
    (l1 l2 : Level) (X : Vec d s b n) :
    nrm2 hb (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X) =
      ip hb X (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X) := by
  change ip hb (act hb t1 t2 _ _ X) (act hb t1 t2 _ _ X) = _
  rw [act_adjoint]
  have h1 : (fun x y => Kernel.kern l1 y x) = Kernel.kern (b := b) l1 := by
    funext x y; exact Kernel.kern_symm l1 y x
  have h2 : (fun x y => Kernel.kern l2 y x) = Kernel.kern (b := b) l2 := by
    funext x y; exact Kernel.kern_symm l2 y x
  rw [h1, h2, act_comp hb ht]
  have hk (l : Level) : localComp hb (Kernel.kern l) (Kernel.kern l) = Kernel.kern (b := b) l := by
    funext x y
    exact (Kernel.expect_kern_mul hb l l x y).trans (if_pos rfl)
  rw [hk, hk]
theorem level_projection_contracts (hb : 0 < b) {t1 t2 : Site s n} (ht : t1 ≠ t2)
    (l1 l2 : Level) (X : Vec d s b n) :
    nrm2 hb (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X) ≤ nrm2 hb X := by
  have he := level_projection_energy hb ht l1 l2 X
  have hc := ip_sq_le hb X (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X)
  have h0 := nrm2_nonneg hb (act hb t1 t2 (Kernel.kern l1) (Kernel.kern l2) X)
  have h1 := nrm2_nonneg hb X
  rw [← he] at hc
  nlinarith
end
end SparseStackV3.Op.PairLeg
