/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# The local signed-bucket space of one site

This file formalizes Section 2.1, *Local space, counts, and the eight families*, of
*SparseStack Is an Optimal Oblivious Subspace Embedding*, Version 3.0 — specifically the
orthogonality relations `new:simplex` and the Jacobi decomposition `new:Jacobi`.

The manuscript works at a site `(g,i)` in `L²({±1} × [b])` with the **uniform probability
measure**, for `b ≥ 2`.  Writing `h = b - 1` and letting `𝔥` be the local hash, it sets

```
  Ω = 1,      e_a = √b · σ · 1_{𝔥 = a},      f_a = (b · 1_{𝔥 = a} - 1) / √(b-1),
```

and records (equation `new:simplex`)

```
  ⟨e_a, e_c⟩ = δ_ac,     ⟨f_a, f_c⟩ = (b δ_ac - 1)/(b-1),     Σ_a f_a = 0,
  Σ_a |f_a⟩⟨f_a| = r_b I_{ℋ₂}   with   r_b = b/(b-1),
```

together with the orthogonality of the three levels `ℋ₀ = ℝΩ`, `ℋ₁ = span{e_a}`,
`ℋ₂ = L²₀([b])`.  It then observes (equation `new:Jacobi`) that multiplication by `e_a`
is the Jacobi operator `J_a = P_a + P_a* + √h (R_a + R_a*)`, which is verified by the three
actions

```
  J_a Ω = e_a,     J_a e_c = δ_ac (Ω + √h f_a),     J_a v = √h ⟨f_a, v⟩ e_a   (v heavy),
```

and that `⟨f_a, v⟩ = v(a)/√(b-1)` for a mean-zero hash function `v`.

Everything here is modelled **concretely**: the local space is the function type
`Fin b × Bool → ℝ` (the `Bool` coordinate carries the sign `σ`), and the inner product is
the explicit finite average `lip`.  No `InnerProductSpace` instance is used, and every
statement below is an elementary finite-sum identity proved outright.

## Main results

* `lip_Omega_Omega`, `lip_Omega_lightVec`, `lip_Omega_heavyVec`, `lip_lightVec_heavyVec` —
  the vacuum/light/heavy levels are mutually orthogonal and `Ω` is a unit vector.
* `lip_lightVec_lightVec`, `lip_heavyVec_heavyVec`, `sum_heavyVec_eq_zero`,
  `sum_heavyVec_frame` (and its outer-product form `sum_heavyVec_outer`) — all four
  identities of equation `new:simplex`, including the tight-frame identity
  `Σ_a |f_a⟩⟨f_a| = r_b I_{ℋ₂}` that supplies the constant `r_b` used throughout
  Sections 3–4.
* `mul_Omega`, `mul_lightVec`, `mul_lift`, `lip_heavyVec_lift` — the three defining actions
  of the Jacobi multiplier `new:Jacobi`.
-/

namespace SparseStackV3.LocalSpace

open Finset

/-- The local space of one site: real functions on `{±1} × [b]`, with the `Bool` coordinate
encoding the sign `σ` and the `Fin b` coordinate the value of the local hash `𝔥`.  This is
the manuscript's `L²({±1} × [b])` as a bare function type. -/
abbrev LocalFn (b : ℕ) : Type := Fin b × Bool → ℝ

/-- The sign character `σ : {±1} → ℝ`, with `true` standing for `+1` and `false` for `-1`. -/
def sgn : Bool → ℝ := fun t => if t then 1 else -1

/-- The inner product of `L²({±1} × [b])` for the **uniform probability measure**: the
average of `f · g` over the `2b` points of `{±1} × [b]`. -/
noncomputable def lip {b : ℕ} (f g : LocalFn b) : ℝ := (∑ x, f x * g x) / (2 * b)

/-- The vacuum vector `Ω = 1` of the manuscript. -/
def Omega (b : ℕ) : LocalFn b := fun _ => 1

/-- The light vector `e_a = √b · σ · 1_{𝔥 = a}` of the manuscript. -/
noncomputable def lightVec {b : ℕ} (a : Fin b) : LocalFn b :=
  fun x => Real.sqrt (b : ℝ) * sgn x.2 * (if x.1 = a then 1 else 0)

/-- The heavy vector `f_a = (b · 1_{𝔥 = a} - 1)/√(b-1)` of the manuscript. -/
noncomputable def heavyVec {b : ℕ} (a : Fin b) : LocalFn b :=
  fun x => ((b : ℝ) * (if x.1 = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1)

/-- Multiplication by the light vector `e_a`.  The manuscript's equation `new:Jacobi` asserts
that this operator equals `J_a = P_a + P_a* + √h (R_a + R_a*)`. -/
noncomputable def mul {b : ℕ} (a : Fin b) (f : LocalFn b) : LocalFn b := fun x => lightVec a x * f x

/-- The lift of a function of the bucket alone to the local space; the manuscript's heavy
vectors are exactly the lifts of mean-zero hash functions `v ∈ L²₀([b])`. -/
def lift {b : ℕ} (v : Fin b → ℝ) : LocalFn b := fun x => v x.1

/-! ### Elementary arithmetic facts about `b ≥ 2` -/

/-- `b ≥ 2` gives `(b : ℝ) ≥ 2`. -/
theorem two_le_cast {b : ℕ} (hb : 2 ≤ b) : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb

/-- `b ≥ 2` gives `(b : ℝ) ≠ 0`. -/
theorem cast_ne_zero {b : ℕ} (hb : 2 ≤ b) : (b : ℝ) ≠ 0 := by
  have := two_le_cast hb; linarith

/-- `b ≥ 2` gives `0 < (b : ℝ) - 1`, so `h = b - 1` is a positive real. -/
theorem sub_one_pos {b : ℕ} (hb : 2 ≤ b) : (0 : ℝ) < (b : ℝ) - 1 := by
  have := two_le_cast hb; linarith

/-- `b ≥ 2` gives `(b : ℝ) - 1 ≠ 0`. -/
theorem sub_one_ne_zero {b : ℕ} (hb : 2 ≤ b) : (b : ℝ) - 1 ≠ 0 := ne_of_gt (sub_one_pos hb)

/-- `√(b-1) ≠ 0` for `b ≥ 2`; this is what makes `f_a` well defined. -/
theorem sqrt_sub_one_ne_zero {b : ℕ} (hb : 2 ≤ b) : Real.sqrt ((b : ℝ) - 1) ≠ 0 :=
  Real.sqrt_ne_zero'.mpr (sub_one_pos hb)

/-- `√b · √b = b`. -/
theorem sqrt_mul_sqrt (b : ℕ) : Real.sqrt (b : ℝ) * Real.sqrt (b : ℝ) = (b : ℝ) :=
  Real.mul_self_sqrt (Nat.cast_nonneg b)

/-- `√(b-1) · √(b-1) = b - 1` for `b ≥ 2`. -/
theorem sqrt_sub_one_mul_sqrt_sub_one {b : ℕ} (hb : 2 ≤ b) :
    Real.sqrt ((b : ℝ) - 1) * Real.sqrt ((b : ℝ) - 1) = (b : ℝ) - 1 :=
  Real.mul_self_sqrt (le_of_lt (sub_one_pos hb))

/-- `σ(+1) = 1`. -/
theorem sgn_true : sgn true = 1 := by simp [sgn]

/-- `σ(-1) = -1`. -/
theorem sgn_false : sgn false = -1 := by simp [sgn]

/-- `σ² = 1`: the sign character is a unit. -/
theorem sgn_mul_self (t : Bool) : sgn t * sgn t = 1 := by
  cases t <;> simp [sgn]

/-! ### Finite-sum toolkit -/

/-- A constant sum over `Fin b`. -/
theorem sum_const_fin (b : ℕ) (c : ℝ) : (∑ _h : Fin b, c) = (b : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The bucket indicator sums to one. -/
theorem sum_indicator {b : ℕ} (a : Fin b) :
    (∑ h : Fin b, (if h = a then (1 : ℝ) else 0)) = 1 := by simp

/-- The bucket indicator sums to one in the other variable. -/
theorem sum_indicator' {b : ℕ} (h : Fin b) :
    (∑ a : Fin b, (if h = a then (1 : ℝ) else 0)) = 1 := by simp

/-- Two bucket indicators are orthonormal: `Σ_𝔥 1_{𝔥=a} 1_{𝔥=c} = δ_ac`. -/
theorem sum_indicator_mul {b : ℕ} (a c : Fin b) :
    (∑ h : Fin b, (if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0))
      = (if a = c then (1 : ℝ) else 0) := by
  have e : ∀ h : Fin b, (if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0)
      = (if h = a then (if a = c then (1 : ℝ) else 0) else 0) := by
    intro h
    by_cases h1 : h = a
    · subst h1; simp
    · rw [if_neg h1, if_neg h1, zero_mul]
  calc (∑ h : Fin b, (if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0))
      = ∑ h : Fin b, (if h = a then (if a = c then (1 : ℝ) else 0) else 0) :=
        Finset.sum_congr rfl fun h _ => e h
    _ = (if a = c then (1 : ℝ) else 0) := by simp

/-- The inner product `lip` written as a sum over buckets, the two signs having been summed. -/
theorem lip_eq_sum {b : ℕ} (f g : LocalFn b) :
    lip f g
      = (∑ h : Fin b, (f (h, true) * g (h, true) + f (h, false) * g (h, false))) / (2 * b) := by
  unfold lip
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun h _ => Fintype.sum_bool _

/-- The key bucket computation behind `⟨f_a, f_c⟩`:
`Σ_𝔥 (b 1_{𝔥=a} - 1)(b 1_{𝔥=c} - 1) = b² δ_ac - b`. -/
theorem sum_heavy_core {b : ℕ} (a c : Fin b) :
    (∑ h : Fin b,
        (((b : ℝ) * (if h = a then 1 else 0) - 1) * ((b : ℝ) * (if h = c then 1 else 0) - 1)))
      = (b : ℝ) ^ 2 * (if a = c then (1 : ℝ) else 0) - (b : ℝ) := by
  have e : ∀ h : Fin b,
      (((b : ℝ) * (if h = a then 1 else 0) - 1) * ((b : ℝ) * (if h = c then 1 else 0) - 1))
        = (b : ℝ) ^ 2 * ((if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0))
          - (b : ℝ) * (if h = a then (1 : ℝ) else 0)
          - (b : ℝ) * (if h = c then (1 : ℝ) else 0) + 1 := by
    intro h; ring
  calc (∑ h : Fin b,
          (((b : ℝ) * (if h = a then 1 else 0) - 1) * ((b : ℝ) * (if h = c then 1 else 0) - 1)))
      = ∑ h : Fin b, ((b : ℝ) ^ 2 * ((if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0))
          - (b : ℝ) * (if h = a then (1 : ℝ) else 0)
          - (b : ℝ) * (if h = c then (1 : ℝ) else 0) + 1) :=
        Finset.sum_congr rfl fun h _ => e h
    _ = (b : ℝ) ^ 2 * (if a = c then (1 : ℝ) else 0) - (b : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_indicator_mul,
          sum_indicator, sum_indicator, sum_const_fin]
        ring

/-! ### Equation `new:simplex`: the three levels and their Gram matrices -/

/-- The vacuum is a unit vector: `⟨Ω, Ω⟩ = 1`. -/
theorem lip_Omega_Omega {b : ℕ} (hb : 2 ≤ b) : lip (Omega b) (Omega b) = 1 := by
  have hb0 : (b : ℝ) ≠ 0 := cast_ne_zero hb
  rw [lip_eq_sum]
  have key : (∑ _h : Fin b,
      ((Omega b) (_h, true) * (Omega b) (_h, true)
        + (Omega b) (_h, false) * (Omega b) (_h, false))) = 2 * (b : ℝ) := by
    calc (∑ _h : Fin b, ((Omega b) (_h, true) * (Omega b) (_h, true)
              + (Omega b) (_h, false) * (Omega b) (_h, false)))
        = ∑ _h : Fin b, (2 : ℝ) := Finset.sum_congr rfl fun h _ => by
            show (1 : ℝ) * 1 + 1 * 1 = 2
            norm_num
      _ = 2 * (b : ℝ) := by rw [sum_const_fin]; ring
  rw [key]
  field_simp

/-- `ℋ₀ ⟂ ℋ₁`: the vacuum is orthogonal to every light vector, `⟨Ω, e_a⟩ = 0`. -/
theorem lip_Omega_lightVec {b : ℕ} (a : Fin b) : lip (Omega b) (lightVec a) = 0 := by
  rw [lip_eq_sum]
  have key : (∑ h : Fin b,
      ((Omega b) (h, true) * (lightVec a) (h, true)
        + (Omega b) (h, false) * (lightVec a) (h, false))) = 0 := by
    refine Finset.sum_eq_zero fun h _ => ?_
    show (1 : ℝ) * (Real.sqrt (b : ℝ) * sgn true * (if h = a then 1 else 0))
        + 1 * (Real.sqrt (b : ℝ) * sgn false * (if h = a then 1 else 0)) = 0
    rw [sgn_true, sgn_false]; ring
  rw [key, zero_div]

/-- `ℋ₀ ⟂ ℋ₂`: the vacuum is orthogonal to every heavy vector, `⟨Ω, f_a⟩ = 0`. -/
theorem lip_Omega_heavyVec {b : ℕ} (_hb : 2 ≤ b) (a : Fin b) :
    lip (Omega b) (heavyVec a) = 0 := by
  rw [lip_eq_sum]
  have key : (∑ h : Fin b,
      ((Omega b) (h, true) * (heavyVec a) (h, true)
        + (Omega b) (h, false) * (heavyVec a) (h, false))) = 0 := by
    calc (∑ h : Fin b, ((Omega b) (h, true) * (heavyVec a) (h, true)
              + (Omega b) (h, false) * (heavyVec a) (h, false)))
        = ∑ h : Fin b, (2 / Real.sqrt ((b : ℝ) - 1))
              * ((b : ℝ) * (if h = a then 1 else 0) - 1) :=
          Finset.sum_congr rfl fun h _ => by
            show (1 : ℝ) * (((b : ℝ) * (if h = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
                + 1 * (((b : ℝ) * (if h = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
                = (2 / Real.sqrt ((b : ℝ) - 1)) * ((b : ℝ) * (if h = a then 1 else 0) - 1)
            ring
      _ = 0 := by
          rw [← Finset.mul_sum]
          have h1 : (∑ h : Fin b, ((b : ℝ) * (if h = a then 1 else 0) - 1)) = 0 := by
            have ha : (∑ h : Fin b, ((b : ℝ) * (if h = a then (1 : ℝ) else 0))) = (b : ℝ) := by
              rw [← Finset.mul_sum, sum_indicator, mul_one]
            have hone : (∑ _h : Fin b, (1 : ℝ)) = (b : ℝ) := by
              rw [sum_const_fin]; ring
            rw [Finset.sum_sub_distrib, ha, hone, sub_self]
          rw [h1, mul_zero]
  rw [key, zero_div]

/-- `ℋ₁ ⟂ ℋ₂`: light and heavy vectors are orthogonal, `⟨e_a, f_c⟩ = 0`. -/
theorem lip_lightVec_heavyVec {b : ℕ} (a c : Fin b) : lip (lightVec a) (heavyVec c) = 0 := by
  rw [lip_eq_sum]
  have key : (∑ h : Fin b,
      ((lightVec a) (h, true) * (heavyVec c) (h, true)
        + (lightVec a) (h, false) * (heavyVec c) (h, false))) = 0 := by
    refine Finset.sum_eq_zero fun h _ => ?_
    show (Real.sqrt (b : ℝ) * sgn true * (if h = a then (1 : ℝ) else 0))
          * (((b : ℝ) * (if h = c then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
        + (Real.sqrt (b : ℝ) * sgn false * (if h = a then (1 : ℝ) else 0))
          * (((b : ℝ) * (if h = c then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1)) = 0
    rw [sgn_true, sgn_false]; ring
  rw [key, zero_div]

/-- Equation `new:simplex`, first identity: `⟨e_a, e_c⟩ = δ_ac`, i.e. the light vectors are
orthonormal. -/
theorem lip_lightVec_lightVec {b : ℕ} (hb : 2 ≤ b) (a c : Fin b) :
    lip (lightVec a) (lightVec c) = if a = c then (1 : ℝ) else 0 := by
  have hb0 : (b : ℝ) ≠ 0 := cast_ne_zero hb
  have hsq := sqrt_mul_sqrt b
  rw [lip_eq_sum]
  have key : (∑ h : Fin b,
      ((lightVec a) (h, true) * (lightVec c) (h, true)
        + (lightVec a) (h, false) * (lightVec c) (h, false)))
      = 2 * (b : ℝ) * (if a = c then (1 : ℝ) else 0) := by
    calc (∑ h : Fin b, ((lightVec a) (h, true) * (lightVec c) (h, true)
              + (lightVec a) (h, false) * (lightVec c) (h, false)))
        = ∑ h : Fin b, 2 * (b : ℝ)
            * ((if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl fun h _ => by
            show (Real.sqrt (b : ℝ) * sgn true * (if h = a then (1 : ℝ) else 0))
                  * (Real.sqrt (b : ℝ) * sgn true * (if h = c then (1 : ℝ) else 0))
                + (Real.sqrt (b : ℝ) * sgn false * (if h = a then (1 : ℝ) else 0))
                  * (Real.sqrt (b : ℝ) * sgn false * (if h = c then (1 : ℝ) else 0))
                = 2 * (b : ℝ)
                    * ((if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0))
            rw [sgn_true, sgn_false]
            linear_combination
              (2 * (if h = a then (1 : ℝ) else 0) * (if h = c then (1 : ℝ) else 0)) * hsq
      _ = 2 * (b : ℝ) * (if a = c then (1 : ℝ) else 0) := by
          rw [← Finset.mul_sum, sum_indicator_mul]
  rw [key]
  field_simp

/-- Equation `new:simplex`, second identity: `⟨f_a, f_c⟩ = (b δ_ac - 1)/(b - 1)`.  The heavy
vectors form a simplex. -/
theorem lip_heavyVec_heavyVec {b : ℕ} (hb : 2 ≤ b) (a c : Fin b) :
    lip (heavyVec a) (heavyVec c)
      = ((b : ℝ) * (if a = c then (1 : ℝ) else 0) - 1) / ((b : ℝ) - 1) := by
  have hb0 : (b : ℝ) ≠ 0 := cast_ne_zero hb
  have hb1 : (b : ℝ) - 1 ≠ 0 := sub_one_ne_zero hb
  have hs := sqrt_sub_one_mul_sqrt_sub_one hb
  rw [lip_eq_sum]
  have key : (∑ h : Fin b,
      ((heavyVec a) (h, true) * (heavyVec c) (h, true)
        + (heavyVec a) (h, false) * (heavyVec c) (h, false)))
      = (2 / ((b : ℝ) - 1)) * ((b : ℝ) ^ 2 * (if a = c then (1 : ℝ) else 0) - (b : ℝ)) := by
    calc (∑ h : Fin b, ((heavyVec a) (h, true) * (heavyVec c) (h, true)
              + (heavyVec a) (h, false) * (heavyVec c) (h, false)))
        = ∑ h : Fin b, (2 / ((b : ℝ) - 1))
            * (((b : ℝ) * (if h = a then 1 else 0) - 1)
                * ((b : ℝ) * (if h = c then 1 else 0) - 1)) :=
          Finset.sum_congr rfl fun h _ => by
            show (((b : ℝ) * (if h = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
                  * (((b : ℝ) * (if h = c then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
                + (((b : ℝ) * (if h = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
                  * (((b : ℝ) * (if h = c then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
                = (2 / ((b : ℝ) - 1))
                    * (((b : ℝ) * (if h = a then 1 else 0) - 1)
                        * ((b : ℝ) * (if h = c then 1 else 0) - 1))
            rw [div_mul_div_comm, hs]
            ring
      _ = (2 / ((b : ℝ) - 1)) * ((b : ℝ) ^ 2 * (if a = c then (1 : ℝ) else 0) - (b : ℝ)) := by
          rw [← Finset.mul_sum, sum_heavy_core]
  rw [key]
  field_simp

/-- Equation `new:simplex`, third identity: `Σ_a f_a = 0`, stated pointwise. -/
theorem sum_heavyVec_eq_zero {b : ℕ} (hb : 2 ≤ b) (x : Fin b × Bool) :
    (∑ a : Fin b, heavyVec a x) = 0 := by
  have hsne := sqrt_sub_one_ne_zero hb
  calc (∑ a : Fin b, heavyVec a x)
      = ∑ a : Fin b, (1 / Real.sqrt ((b : ℝ) - 1))
          * ((b : ℝ) * (if x.1 = a then 1 else 0) - 1) :=
        Finset.sum_congr rfl fun a _ => by
          show ((b : ℝ) * (if x.1 = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1)
              = (1 / Real.sqrt ((b : ℝ) - 1)) * ((b : ℝ) * (if x.1 = a then 1 else 0) - 1)
          ring
    _ = 0 := by
        rw [← Finset.mul_sum]
        have ha : (∑ a : Fin b, ((b : ℝ) * (if x.1 = a then (1 : ℝ) else 0))) = (b : ℝ) := by
          rw [← Finset.mul_sum, sum_indicator', mul_one]
        have hone : (∑ _a : Fin b, (1 : ℝ)) = (b : ℝ) := by rw [sum_const_fin]; ring
        rw [Finset.sum_sub_distrib, ha, hone, sub_self, mul_zero]

/-! ### Equation `new:Jacobi`: the three actions of multiplication by `e_a` -/

/-- Equation `new:Jacobi`, first action: `J_a Ω = e_a`. -/
theorem mul_Omega {b : ℕ} (a : Fin b) : mul a (Omega b) = lightVec a := by
  funext x
  show lightVec a x * 1 = lightVec a x
  exact mul_one _

/-- Equation `new:Jacobi`, second action: `J_a e_c = δ_ac (Ω + √h f_a)` with `h = b - 1`. -/
theorem mul_lightVec {b : ℕ} (hb : 2 ≤ b) (a c : Fin b) :
    mul a (lightVec c)
      = fun x => (if a = c then (1 : ℝ) else 0)
          * (Omega b x + Real.sqrt ((b : ℝ) - 1) * heavyVec a x) := by
  have hsne := sqrt_sub_one_ne_zero hb
  have hsq := sqrt_mul_sqrt b
  funext x
  have hR : Real.sqrt ((b : ℝ) - 1)
      * (((b : ℝ) * (if x.1 = a then (1 : ℝ) else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
      = (b : ℝ) * (if x.1 = a then (1 : ℝ) else 0) - 1 := by
    field_simp
  show (Real.sqrt (b : ℝ) * sgn x.2 * (if x.1 = a then (1 : ℝ) else 0))
      * (Real.sqrt (b : ℝ) * sgn x.2 * (if x.1 = c then (1 : ℝ) else 0))
      = (if a = c then (1 : ℝ) else 0)
        * (1 + Real.sqrt ((b : ℝ) - 1)
            * (((b : ℝ) * (if x.1 = a then (1 : ℝ) else 0) - 1) / Real.sqrt ((b : ℝ) - 1)))
  rw [hR]
  have hsg := sgn_mul_self x.2
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl]
    by_cases hx : x.1 = a
    · rw [if_pos hx]
      linear_combination (sgn x.2 * sgn x.2) * hsq + (b : ℝ) * hsg
    · rw [if_neg hx]; ring
  · rw [if_neg hac]
    by_cases hx : x.1 = a
    · have hxc : ¬ (x.1 = c) := fun hh => hac (hx.symm.trans hh)
      rw [if_pos hx, if_neg hxc]; ring
    · rw [if_neg hx]; ring

/-- The pairing of a heavy vector with a mean-zero hash function:
`⟨f_a, v⟩ = v(a)/√(b-1)`.  This is the identity the manuscript uses to prove the frame
identity `Σ_a |f_a⟩⟨f_a| = r_b I`. -/
theorem lip_heavyVec_lift {b : ℕ} (hb : 2 ≤ b) (a : Fin b) (v : Fin b → ℝ)
    (hv : (∑ h : Fin b, v h) = 0) :
    lip (heavyVec a) (lift v) = v a / Real.sqrt ((b : ℝ) - 1) := by
  have hb0 : (b : ℝ) ≠ 0 := cast_ne_zero hb
  have hsne := sqrt_sub_one_ne_zero hb
  rw [lip_eq_sum]
  have key : (∑ h : Fin b,
      ((heavyVec a) (h, true) * (lift v) (h, true)
        + (heavyVec a) (h, false) * (lift v) (h, false)))
      = (2 / Real.sqrt ((b : ℝ) - 1)) * ((b : ℝ) * v a) := by
    calc (∑ h : Fin b, ((heavyVec a) (h, true) * (lift v) (h, true)
              + (heavyVec a) (h, false) * (lift v) (h, false)))
        = ∑ h : Fin b, (2 / Real.sqrt ((b : ℝ) - 1))
            * (((b : ℝ) * (if h = a then 1 else 0) - 1) * v h) :=
          Finset.sum_congr rfl fun h _ => by
            show (((b : ℝ) * (if h = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1)) * v h
                + (((b : ℝ) * (if h = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1)) * v h
                = (2 / Real.sqrt ((b : ℝ) - 1))
                    * (((b : ℝ) * (if h = a then 1 else 0) - 1) * v h)
            ring
      _ = (2 / Real.sqrt ((b : ℝ) - 1)) * ((b : ℝ) * v a) := by
          rw [← Finset.mul_sum]
          congr 1
          calc (∑ h : Fin b, (((b : ℝ) * (if h = a then (1 : ℝ) else 0) - 1) * v h))
              = ∑ h : Fin b, ((b : ℝ) * ((if h = a then (1 : ℝ) else 0) * v h) - v h) :=
                Finset.sum_congr rfl fun h _ => by ring
            _ = (b : ℝ) * v a := by
                have hvi : (∑ h : Fin b, ((if h = a then (1 : ℝ) else 0) * v h)) = v a := by
                  simp [ite_mul]
                rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hvi, hv, sub_zero]
  rw [key]
  field_simp

/-- **The fourth identity of equation `new:simplex`:**
`Σ_a |f_a⟩⟨f_a| = r_b I_{ℋ₂}` with `r_b = b/(b-1)`.

A vector of the heavy space `ℋ₂ = L²₀([b])` is exactly a mean-zero function
`v` of the bucket alone, lifted by `lift`; the identity says that applying
`Σ_a |f_a⟩⟨f_a|` to it returns `r_b` times it.  The manuscript's proof is
recorded verbatim: "a mean-zero hash function `v` satisfies
`⟨f_a, v⟩ = v(a)/√(b-1)`; summing its squared values proves the frame
identity" — the first half is `lip_heavyVec_lift`, and the sum is done here. -/
theorem sum_heavyVec_frame {b : ℕ} (hb : 2 ≤ b) (v : Fin b → ℝ)
    (hv : (∑ h : Fin b, v h) = 0) (x : Fin b × Bool) :
    (∑ a : Fin b, lip (heavyVec a) (lift v) * heavyVec a x)
      = ((b : ℝ) / ((b : ℝ) - 1)) * lift v x := by
  have hsne := sqrt_sub_one_ne_zero hb
  have hs := sqrt_sub_one_mul_sqrt_sub_one hb
  have hne := sub_one_ne_zero hb
  have hstep : ∀ a : Fin b,
      lip (heavyVec a) (lift v) * heavyVec a x
        = (v a * ((b : ℝ) * (if x.1 = a then 1 else 0) - 1)) / ((b : ℝ) - 1) := by
    intro a
    rw [lip_heavyVec_lift hb a v hv]
    show v a / Real.sqrt ((b : ℝ) - 1)
        * (((b : ℝ) * (if x.1 = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
      = _
    rw [div_mul_div_comm, hs]
  simp only [hstep]
  rw [← Finset.sum_div]
  have key : (∑ a : Fin b, v a * ((b : ℝ) * (if x.1 = a then 1 else 0) - 1))
      = (b : ℝ) * v x.1 := by
    have hexp : ∀ a : Fin b,
        v a * ((b : ℝ) * (if x.1 = a then 1 else 0) - 1)
          = (b : ℝ) * ((if x.1 = a then (1 : ℝ) else 0) * v a) - v a := by
      intro a
      by_cases h : x.1 = a
      · rw [if_pos h]; ring
      · rw [if_neg h]; ring
    simp only [hexp]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hv, sub_zero]
    congr 1
    simp [ite_mul]
  rw [key]
  show (b : ℝ) * v x.1 / ((b : ℝ) - 1) = (b : ℝ) / ((b : ℝ) - 1) * v x.1
  field_simp

/-- The same frame identity in "outer product" form:
`Σ_a f_a(x) f_a(y) = r_b · (b·1{hₓ = h_y} − 1)`, i.e. `r_b` times the
reproducing kernel of the heavy space. -/
theorem sum_heavyVec_outer {b : ℕ} (hb : 2 ≤ b) (x y : Fin b × Bool) :
    (∑ a : Fin b, heavyVec a x * heavyVec a y)
      = ((b : ℝ) / ((b : ℝ) - 1))
        * ((b : ℝ) * (if x.1 = y.1 then 1 else 0) - 1) := by
  have hs := sqrt_sub_one_mul_sqrt_sub_one hb
  have hne := sub_one_ne_zero hb
  have hflip : ∀ c a : Fin b,
      (if c = a then (1 : ℝ) else 0) = (if a = c then (1 : ℝ) else 0) := by
    intro c a
    by_cases h : c = a
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  have hstep : ∀ a : Fin b,
      heavyVec a x * heavyVec a y
        = (((b : ℝ) * (if a = x.1 then 1 else 0) - 1)
            * ((b : ℝ) * (if a = y.1 then 1 else 0) - 1)) / ((b : ℝ) - 1) := by
    intro a
    show (((b : ℝ) * (if x.1 = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1))
        * (((b : ℝ) * (if y.1 = a then 1 else 0) - 1) / Real.sqrt ((b : ℝ) - 1)) = _
    rw [div_mul_div_comm, hs, hflip x.1 a, hflip y.1 a]
  simp only [hstep]
  rw [← Finset.sum_div, sum_heavy_core x.1 y.1]
  have hb0 : (b : ℝ) ≠ 0 := cast_ne_zero hb
  by_cases h : x.1 = y.1
  · rw [if_pos h]; field_simp
  · rw [if_neg h]; field_simp

/-- Equation `new:Jacobi`, third action: for a heavy vector `v` (a mean-zero function of the
bucket alone), `J_a v = √h ⟨f_a, v⟩ e_a` with `h = b - 1`. -/
theorem mul_lift {b : ℕ} (hb : 2 ≤ b) (a : Fin b) (v : Fin b → ℝ)
    (hv : (∑ h : Fin b, v h) = 0) :
    mul a (lift v)
      = fun x => Real.sqrt ((b : ℝ) - 1) * lip (heavyVec a) (lift v) * lightVec a x := by
  have hsne := sqrt_sub_one_ne_zero hb
  rw [lip_heavyVec_lift hb a v hv]
  have hc : Real.sqrt ((b : ℝ) - 1) * (v a / Real.sqrt ((b : ℝ) - 1)) = v a := by
    field_simp
  funext x
  rw [hc]
  show Real.sqrt (b : ℝ) * sgn x.2 * (if x.1 = a then (1 : ℝ) else 0) * v x.1
      = v a * (Real.sqrt (b : ℝ) * sgn x.2 * (if x.1 = a then (1 : ℝ) else 0))
  by_cases hx : x.1 = a
  · rw [hx]; ring
  · rw [if_neg hx]; ring

end SparseStackV3.LocalSpace
