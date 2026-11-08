/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedCertificate.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-! # Integer combinations of physical F0 triangles

`Realizes p G f w` says that the integer edge function `f : Sym2 V → ℤ` is, at **every**
`e : Sym2 V`, the signed sum `∑ s, c s * [e ∈ triEdges s]` of a coefficient function
`c : Finset V → ℤ` supported on actual F0 copies of `G`, with `∑ s, |c s| ≤ w`.

The predicate is closed under sums, integer multiples and pointwise equality, contains every
actual F0 triangle with cost `1`, and for `f = ind P` it yields exactly a
`SignedCertificate.IsSignedCert` with `certWeight ≤ w` (`Realizes.signedCert`).
Every `Realizes` function has zero F0 charge `crossing - 2·internal` (`Realizes.charge_eq_zero`).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.IntegerCertificate
open Finset SignedCertificate TypedApplicationLinks
section Edges
variable {V : Type*} [DecidableEq V]
/-- Indicator of a single unordered pair. -/
def edgeOf (e : Sym2 V) : Sym2 V → ℤ := fun e' => if e' = e then 1 else 0
/-- Indicator of the pair `{x, y}`. -/
def edgeInd (x y : V) : Sym2 V → ℤ := edgeOf s(x, y)
end Edges
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
/-- `f` is an integer combination of actual F0 triangles of `G` of total weight `≤ w`. -/
def Realizes (p : V → Fin 2) (G : SimpleGraph V) (f : Sym2 V → ℤ) (w : ℤ) : Prop :=
  ∃ c : Finset V → ℤ, (∀ s, c s ≠ 0 → IsCopy p F0 G s) ∧
    (∀ e, f e = ∑ s, c s * ind (triEdges s) e) ∧ ∑ s, |c s| ≤ w
variable {p : V → Fin 2} {G : SimpleGraph V}
namespace Realizes
theorem zero : Realizes p G 0 0 :=
  ⟨0, by simp, by simp, by simp⟩
theorem congr {f g : Sym2 V → ℤ} {w : ℤ} (h : Realizes p G f w) (hfg : f = g) :
    Realizes p G g w := hfg ▸ h
theorem mono {f : Sym2 V → ℤ} {w w' : ℤ} (h : Realizes p G f w) (hw : w ≤ w') :
    Realizes p G f w' := by
  obtain ⟨c, h1, h2, h3⟩ := h
  exact ⟨c, h1, h2, h3.trans hw⟩
theorem add {f g : Sym2 V → ℤ} {w w' : ℤ} (hf : Realizes p G f w) (hg : Realizes p G g w') :
    Realizes p G (f + g) (w + w') := by
  obtain ⟨c, h1, h2, h3⟩ := hf
  obtain ⟨d, k1, k2, k3⟩ := hg
  refine ⟨c + d, fun s hs => ?_, fun e => ?_, ?_⟩
  · by_cases hc : c s = 0
    · exact k1 s (by simpa [hc] using hs)
    · exact h1 s hc
  · simp only [Pi.add_apply, h2 e, k2 e, add_mul, sum_add_distrib]
  · calc ∑ s, |(c + d) s| ≤ ∑ s, (|c s| + |d s|) :=
          Finset.sum_le_sum fun s _ => abs_add_le _ _
      _ = ∑ s, |c s| + ∑ s, |d s| := sum_add_distrib
      _ ≤ w + w' := add_le_add h3 k3
theorem smul {f : Sym2 V → ℤ} {w : ℤ} (k : ℤ) (h : Realizes p G f w) :
    Realizes p G (k • f) (|k| * w) := by
  obtain ⟨c, h1, h2, h3⟩ := h
  refine ⟨k • c, fun s hs => h1 s ?_, fun e => ?_, ?_⟩
  · intro hc; apply hs; simp [hc]
  · simp only [Pi.smul_apply, smul_eq_mul, h2 e, mul_sum, mul_assoc]
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ← mul_sum]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg k)
theorem neg {f : Sym2 V → ℤ} {w : ℤ} (h : Realizes p G f w) : Realizes p G (-f) w := by
  have := h.smul (-1)
  simpa using this
theorem sub {f g : Sym2 V → ℤ} {w w' : ℤ} (hf : Realizes p G f w) (hg : Realizes p G g w') :
    Realizes p G (f - g) (w + w') := by
  simpa [sub_eq_add_neg] using hf.add hg.neg
theorem sum {α : Type*} (S : Finset α) (f : α → Sym2 V → ℤ) (w : α → ℤ)
    (h : ∀ i ∈ S, Realizes p G (f i) (w i)) :
    Realizes p G (∑ i ∈ S, f i) (∑ i ∈ S, w i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (zero : Realizes p G 0 0)
  | insert a S ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a S)).add (ih fun i hi => h i (mem_insert_of_mem hi))
theorem tri {s : Finset V} (hs : IsCopy p F0 G s) : Realizes p G (ind (triEdges s)) 1 := by
  refine ⟨fun t => if t = s then 1 else 0, fun t ht => ?_, fun e => ?_, ?_⟩
  · by_cases h : t = s
    · exact h ▸ hs
    · simp [h] at ht
  · simp
  · simp [apply_ite]
end Realizes
/-! ### Triangles in terms of edges -/
def kappa (p : V → Fin 2) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => if p a = p b then -2 else 1, by
    intro a b; by_cases h : p a = p b <;> simp [h, eq_comm]⟩
/-- The F0 charge `crossing - 2·internal` of an integer edge function. -/
def charge (p : V → Fin 2) (f : Sym2 V → ℤ) : ℤ := ∑ e, f e * kappa p e
end PartitionedTriangleAbsorption.IntegerCertificate
