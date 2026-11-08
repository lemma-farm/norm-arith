/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Bugeaud2013.Convergents
public import DiophantineApproximation.StammeringWords
public import Mathlib
public import Mathlib.NumberTheory.Real.Irrational

-- Used only inside proofs.
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The value of an infinite continued fraction `α = [0; a₁, a₂, …]` (Bugeaud 2013, §§2–3)

For a sequence `a₁, a₂, …` of positive integers, the convergents `p_ℓ / q_ℓ` of `Convergents.lean`
converge to a real number `α = [0; a₁, a₂, …]`. This file defines `α` (as the supremum of the even
convergents), proves that it is the limit of all convergents, and derives the facts that §3 of the
paper uses: the approximation property (2.2), irrationality, the estimate behind (3.1) for two
sequences with a common prefix, and the quadratic polynomial `P_n` of an eventually periodic
continued fraction (Perron, p. 71).

The value depends only on `a₁, a₂, …`; the value `a 0` is never used.

## Main definitions

* `Nat.contConv a ℓ`: the convergent `p_ℓ / q_ℓ` as a real number.
* `Nat.contFrac a`: `α = [0; a₁, a₂, …]`.

## Main results

* `Nat.tendsto_contConv`: `p_ℓ / q_ℓ → α`.
* `Nat.abs_contFrac_sub_contConv_lt`: `|α - p_ℓ / q_ℓ| < 1 / (q_ℓ q_{ℓ+1})`, with `α` strictly
  between consecutive convergents (`Nat.contFrac_strictBetween`).
* `Nat.abs_contDen_mul_contFrac_sub_lt`: **(2.2)** `|q_ℓ α - p_ℓ| < q_{ℓ+1}⁻¹`.
* `Nat.contFrac_pos`, `Nat.contFrac_lt_one`, `Nat.irrational_contFrac`: `α ∈ (0, 1)` is
  irrational.
* `Nat.abs_contFrac_sub_contFrac_lt`: two sequences that agree on `a₁, …, a_ℓ` have values at
  distance `< 2 / q_ℓ²` (the estimate behind (3.1)).
* `Nat.contFrac_eq_of_tail`: `α = (p_k + p_{k-1} α_k) / (q_k + q_{k-1} α_k)` with
  `α_k = [0; a_{k+1}, a_{k+2}, …]`.
* `Nat.contFrac_isRoot`: **the polynomial `P_n` of §3**: if `a` is periodic with period `r` from
  the index `w + 1` on (`w ≥ 1`), then `α` is a root of
  `(q_{w-1} q_{w+r} - q_w q_{w+r-1}) X² - (q_{w-1} p_{w+r} - q_w p_{w+r-1} + p_{w-1} q_{w+r} -
  p_w q_{w+r-1}) X + (p_{w-1} p_{w+r} - p_w p_{w+r-1})`, whose leading coefficient is non-zero.
* `Nat.exists_quadratic_of_isEventuallyPeriodic`: an eventually periodic continued fraction is a
  quadratic irrational (Euler).

## References

Y. Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm.
Supér. (4) **46** (2013), 1005–1022, §§2–3; O. Perron, *Die Lehre von den Kettenbrüchen*, 1929.
-/

@[expose] public section

open Filter Topology

namespace Nat

/-- **The convergent** `p_ℓ / q_ℓ` of `[0; a₁, a₂, …]`, as a real number. -/
noncomputable def contConv (a : ℕ → ℕ) (n : ℕ) : ℝ := contNum a n / contDen a n

/-- **The continued fraction** `α = [0; a₁, a₂, …]`, defined as the supremum of the even
convergents `p_{2k} / q_{2k}`. For positive `a_ℓ` it is the limit of all convergents
(`Nat.tendsto_contConv`). -/
noncomputable def contFrac (a : ℕ → ℕ) : ℝ := ⨆ k, contConv a (2 * k)

variable {a b : ℕ → ℕ}

/-! ### Dependence on a prefix -/

                                          
                                                                                              
                                   
                                                
             
                
              
              
              
                                                                                                
                                         

                                          
                                                                                              
                                   
                                                
             
                
              
                                    
              
                                                                                                
                                         

                                                                                               
                                     
                                                                           

                                       
                                                                                   
                 
         
          
                                                                     

                             

                                                                                              
                                                                                                

                                                                                      
                                                     
theorem contNum_add (a : ℕ → ℕ) (j n : ℕ) :
    contNum a (j + 1 + n) = contNum a (j + 1) * contDen (fun i ↦ a (i + (j + 1))) n +
      contNum a j * contNum (fun i ↦ a (i + (j + 1))) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 =>
      rw [show j + 1 + 1 = j + 2 by ring, contNum_add_two, contDen_one, contNum_one,
        show 1 + (j + 1) = j + 2 by ring]
      ring
    | n + 2 =>
      rw [show j + 1 + (n + 2) = j + 1 + n + 2 by ring, contNum_add_two, contDen_add_two,
        contNum_add_two, show j + 1 + n + 1 = j + 1 + (n + 1) by ring, ih n (by omega),
        ih (n + 1) (by omega), show n + 2 + (j + 1) = j + 1 + n + 2 by ring]
      ring

/-- `q_{k+n} = q_k q'_n + q_{k-1} p'_n`, where `p'/q'` are the convergents of the tail
`[0; a_{k+1}, a_{k+2}, …]`; stated at `k = j + 1`. -/
theorem contDen_add (a : ℕ → ℕ) (j n : ℕ) :
    contDen a (j + 1 + n) = contDen a (j + 1) * contDen (fun i ↦ a (i + (j + 1))) n +
      contDen a j * contNum (fun i ↦ a (i + (j + 1))) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 =>
      rw [show j + 1 + 1 = j + 2 by ring, contDen_add_two, contDen_one, contNum_one,
        show 1 + (j + 1) = j + 2 by ring]
      ring
    | n + 2 =>
      rw [show j + 1 + (n + 2) = j + 1 + n + 2 by ring, contDen_add_two, contDen_add_two,
        contNum_add_two, show j + 1 + n + 1 = j + 1 + (n + 1) by ring, ih n (by omega),
        ih (n + 1) (by omega), show n + 2 + (j + 1) = j + 1 + n + 2 by ring]
      ring

section Positive

/-! The partial quotients are positive integers: `a_ℓ ≥ 1` for `ℓ ≥ 1`. -/

variable (ha : ∀ n, 1 ≤ a (n + 1))
include ha

theorem contDen_pos_real (n : ℕ) : (0 : ℝ) < contDen a n := by
  exact_mod_cast contDen_pos ha n

/-- `q_ℓ ≥ ℓ`. -/
theorem le_contDen (n : ℕ) : n ≤ contDen a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simpa using ha 0
    | n + 2 =>
      rw [contDen_add_two]
      have h1 := ha (n + 1)
      have h2 := ih (n + 1) (by omega)
      have h3 := one_le_contDen ha n
      nlinarith

                                      
                                                                          
                                         
                                             
                                               
                                                                         

                                                                
theorem contConv_succ_sub (n : ℕ) :
    contConv a (n + 1) - contConv a n = (-1) ^ n / (contDen a n * contDen a (n + 1)) := by
  have h : (contNum a (n + 1) : ℝ) * contDen a n - contNum a n * contDen a (n + 1) = (-1) ^ n := by
    exact_mod_cast contNum_mul_contDen_sub a n
  have h0 := (contDen_pos_real ha n).ne'
  have h1 := (contDen_pos_real ha (n + 1)).ne'
  unfold contConv
  field_simp
  linear_combination h

/-- `p_{ℓ+2} / q_{ℓ+2} - p_ℓ / q_ℓ = (-1)^ℓ a_{ℓ+2} / (q_ℓ q_{ℓ+2})`. -/
theorem contConv_add_two_sub (n : ℕ) :
    contConv a (n + 2) - contConv a n =
      (-1) ^ n * a (n + 2) / (contDen a n * contDen a (n + 2)) := by
  have h : (contNum a (n + 1) : ℝ) * contDen a n - contNum a n * contDen a (n + 1) = (-1) ^ n := by
    exact_mod_cast contNum_mul_contDen_sub a n
  have h0 := (contDen_pos_real ha n).ne'
  have h2 := (contDen_pos_real ha (n + 2)).ne'
  unfold contConv
  field_simp
  rw [contNum_add_two, contDen_add_two]
  push_cast
  linear_combination (a (n + 2) : ℝ) * h

/-- The even convergents increase strictly. -/
theorem contConv_two_mul_lt (k : ℕ) : contConv a (2 * k) < contConv a (2 * (k + 1)) := by
  have h := contConv_add_two_sub ha (2 * k)
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul] at h
  have := contDen_pos_real ha (2 * k)
  have := contDen_pos_real ha (2 * (k + 1))
  have ha' : (0 : ℝ) < a (2 * (k + 1)) := by exact_mod_cast ha (2 * k + 1)
  have : 0 < contConv a (2 * (k + 1)) - contConv a (2 * k) := by
    rw [h]; norm_num; positivity
  linarith

/-- The odd convergents decrease strictly. -/
theorem contConv_two_mul_add_one_lt (k : ℕ) :
    contConv a (2 * (k + 1) + 1) < contConv a (2 * k + 1) := by
  have h := contConv_add_two_sub ha (2 * k + 1)
  rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, pow_succ, pow_mul] at h
  have := contDen_pos_real ha (2 * k + 1)
  have := contDen_pos_real ha (2 * (k + 1) + 1)
  have ha' : (0 : ℝ) < a (2 * (k + 1) + 1) := by exact_mod_cast ha (2 * (k + 1))
  have : contConv a (2 * (k + 1) + 1) - contConv a (2 * k + 1) < 0 := by
    rw [h, neg_one_sq, one_pow, one_mul, neg_one_mul, neg_div]
    exact neg_neg_of_pos (by positivity)
  linarith

theorem contConv_two_mul_lt_succ (k : ℕ) : contConv a (2 * k) < contConv a (2 * k + 1) := by
  have h := contConv_succ_sub ha (2 * k)
  rw [pow_mul] at h
  have := contDen_pos_real ha (2 * k)
  have := contDen_pos_real ha (2 * k + 1)
  have : 0 < contConv a (2 * k + 1) - contConv a (2 * k) := by
    rw [h]; norm_num; positivity
  linarith

/-- Every even convergent lies below every odd one. -/
theorem contConv_two_mul_lt_odd (k j : ℕ) : contConv a (2 * k) < contConv a (2 * j + 1) := by
  have hmono : StrictMono fun k ↦ contConv a (2 * k) :=
    strictMono_nat_of_lt_succ (contConv_two_mul_lt ha)
  have hanti : StrictAnti fun k ↦ contConv a (2 * k + 1) :=
    strictAnti_nat_of_succ_lt (contConv_two_mul_add_one_lt ha)
  calc contConv a (2 * k) ≤ contConv a (2 * max k j) := hmono.monotone (le_max_left k j)
    _ < contConv a (2 * max k j + 1) := contConv_two_mul_lt_succ ha _
    _ ≤ contConv a (2 * j + 1) := hanti.antitone (le_max_right k j)

theorem bddAbove_contConv_two_mul : BddAbove (Set.range fun k ↦ contConv a (2 * k)) :=
  ⟨contConv a 1, by rintro _ ⟨k, rfl⟩; simpa using (contConv_two_mul_lt_odd ha k 0).le⟩

/-- The even convergents lie strictly below `α`. -/
theorem contConv_two_mul_lt_contFrac (k : ℕ) : contConv a (2 * k) < contFrac a :=
  (contConv_two_mul_lt ha k).trans_le (le_ciSup (bddAbove_contConv_two_mul ha) (k + 1))

/-- The odd convergents lie strictly above `α`. -/
theorem contFrac_lt_contConv_odd (j : ℕ) : contFrac a < contConv a (2 * j + 1) :=
  (ciSup_le fun k ↦ (contConv_two_mul_lt_odd ha k (j + 1)).le).trans_lt
    (contConv_two_mul_add_one_lt ha j)

/-- **`α` lies strictly between consecutive convergents.** -/
theorem contFrac_strictBetween (n : ℕ) :
    (contConv a n < contFrac a ∧ contFrac a < contConv a (n + 1)) ∨
      (contConv a (n + 1) < contFrac a ∧ contFrac a < contConv a n) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact Or.inl ⟨contConv_two_mul_lt_contFrac ha k, contFrac_lt_contConv_odd ha k⟩
  · right
    refine ⟨?_, contFrac_lt_contConv_odd ha k⟩
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    exact contConv_two_mul_lt_contFrac ha (k + 1)

theorem contFrac_ne_contConv (n : ℕ) : contFrac a ≠ contConv a n := by
  rcases contFrac_strictBetween ha n with h | h
  · exact h.1.ne'
  · exact h.2.ne

/-- `|α - p_ℓ / q_ℓ| < 1 / (q_ℓ q_{ℓ+1})`. -/
theorem abs_contFrac_sub_contConv_lt (n : ℕ) :
    |contFrac a - contConv a n| < 1 / (contDen a n * contDen a (n + 1)) := by
  have h := contConv_succ_sub ha n
  have hq := mul_pos (contDen_pos_real ha n) (contDen_pos_real ha (n + 1))
  rcases neg_one_pow_eq_or ℝ n with hn | hn <;> rw [hn] at h <;>
    rcases contFrac_strictBetween ha n with h' | h' <;> rw [abs_lt]
  · constructor <;> linarith
  · -- impossible: `p_{ℓ+1}/q_{ℓ+1} > p_ℓ/q_ℓ`
    have : 0 < 1 / (contDen a n * contDen a (n + 1) : ℝ) := by positivity
    linarith [h'.1, h'.2]
  · have : 0 < 1 / (contDen a n * contDen a (n + 1) : ℝ) := by positivity
    have h2 : contConv a (n + 1) - contConv a n = -(1 / (contDen a n * contDen a (n + 1))) := by
      rw [h]; ring
    linarith [h'.1, h'.2]
  · have h2 : contConv a (n + 1) - contConv a n = -(1 / (contDen a n * contDen a (n + 1))) := by
      rw [h]; ring
    constructor <;> linarith

                                    
                                                 
                                                                 
                                                        
                                  
                                                       
                                               
         
        

                                                                                                
        
theorem abs_contDen_mul_contFrac_sub_lt (n : ℕ) :
    |contDen a n * contFrac a - contNum a n| < (contDen a (n + 1) : ℝ)⁻¹ := by
  have h0 := contDen_pos_real ha n
  have h1 := contDen_pos_real ha (n + 1)
  have h := abs_contFrac_sub_contConv_lt ha n
  have e : (contDen a n : ℝ) * contFrac a - contNum a n =
      contDen a n * (contFrac a - contConv a n) := by
    unfold contConv; field_simp
  rw [e, abs_mul, abs_of_pos h0]
  calc (contDen a n : ℝ) * |contFrac a - contConv a n|
      < contDen a n * (1 / (contDen a n * contDen a (n + 1))) := by gcongr
    _ = (contDen a (n + 1) : ℝ)⁻¹ := by field_simp

/-- **The convergents tend to `α`.** -/
theorem tendsto_contConv : Tendsto (contConv a) atTop (𝓝 (contFrac a)) := by
  have hb (n : ℕ) : |contFrac a - contConv a n| ≤ 1 / ((n : ℝ) + 1) := by
    refine (abs_contFrac_sub_contConv_lt ha n).le.trans ?_
    have h0 : (1 : ℝ) ≤ contDen a n := by exact_mod_cast one_le_contDen ha n
    have h1 : (n : ℝ) + 1 ≤ contDen a (n + 1) := by exact_mod_cast le_contDen ha (n + 1)
    gcongr
    nlinarith
  have T := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have L : Tendsto (fun n : ℕ ↦ contFrac a - 1 / ((n : ℝ) + 1)) atTop (𝓝 (contFrac a)) := by
    simpa using (tendsto_const_nhds (x := contFrac a)).sub T
  have U : Tendsto (fun n : ℕ ↦ contFrac a + 1 / ((n : ℝ) + 1)) atTop (𝓝 (contFrac a)) := by
    simpa using (tendsto_const_nhds (x := contFrac a)).add T
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le L U (fun n ↦ ?_) (fun n ↦ ?_)
  · linarith [(abs_le.mp (hb n)).2]
  · linarith [(abs_le.mp (hb n)).1]

/-- `α > 0`. -/
theorem contFrac_pos : 0 < contFrac a := by
  simpa [contConv] using contConv_two_mul_lt_contFrac ha 0

/-- `α ≤ 1 / a₁`, strictly. -/
theorem contFrac_lt_inv : contFrac a < (a 1 : ℝ)⁻¹ := by
  simpa [contConv] using contFrac_lt_contConv_odd ha 0

/-- `α < 1`. -/
theorem contFrac_lt_one : contFrac a < 1 := by
  refine (contFrac_lt_inv ha).trans_le (inv_le_one_of_one_le₀ ?_)
  exact_mod_cast ha 0

/-- **`α` is irrational.** -/
theorem irrational_contFrac : Irrational (contFrac a) := by
  rintro ⟨x, hx⟩
  set d := x.den
  have hd : (0 : ℝ) < d := by exact_mod_cast x.den_pos
  have hx' : contFrac a = x.num / d := by rw [← hx, Rat.cast_def]
  have h := abs_contDen_mul_contFrac_sub_lt ha d
  have hq : (d : ℝ) + 1 ≤ contDen a (d + 1) := by exact_mod_cast le_contDen ha (d + 1)
  set z : ℤ := contDen a d * x.num - contNum a d * d
  have hz : (contDen a d : ℝ) * contFrac a - contNum a d = z / d := by
    rw [hx']; simp only [z]; push_cast; field_simp
  rw [hz, abs_div, abs_of_pos hd] at h
  have hz1 : |(z : ℝ)| < 1 := by
    have hq0 : (0 : ℝ) < contDen a (d + 1) := by linarith
    rw [div_lt_iff₀ hd] at h
    calc |(z : ℝ)| < (contDen a (d + 1) : ℝ)⁻¹ * d := h
      _ ≤ (contDen a (d + 1) : ℝ)⁻¹ * contDen a (d + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hq0.le)
      _ = 1 := inv_mul_cancel₀ hq0.ne'
  have hz0 : z = 0 := by
    have : |z| < 1 := by exact_mod_cast hz1
    exact Int.abs_lt_one_iff.mp this
  apply contFrac_ne_contConv ha d
  have hq0 := contDen_pos_real ha d
  have : (contDen a d : ℝ) * x.num = contNum a d * d := by
    have : ((z : ℤ) : ℝ) = 0 := by exact_mod_cast hz0
    simp only [z] at this; push_cast at this; linarith
  rw [hx', contConv]
  field_simp
  linarith

                                                                                              
                               
                                                                      
                                          
                                                               
                                                 
                                                 
                                                                          
                                
                                                                       
                                                              
                                                                            
                                            

                                                                              
                                                           
theorem contFrac_eq_of_tail (j : ℕ) :
    contFrac a = (contNum a (j + 1) + contNum a j * contFrac (fun i ↦ a (i + (j + 1)))) /
      (contDen a (j + 1) + contDen a j * contFrac (fun i ↦ a (i + (j + 1)))) := by
  set s : ℕ → ℕ := fun i ↦ a (i + (j + 1)) with hsdef
  have hs : ∀ n, 1 ≤ s (n + 1) := fun n ↦ ha (n + 1 + j)
  have hQ : (0 : ℝ) < contDen a (j + 1) + contDen a j * contFrac s := by
    have := contDen_pos_real ha (j + 1)
    have := contDen_pos_real ha j
    have := contFrac_pos hs
    positivity
  have T1 : Tendsto (fun n ↦ contConv a (n + (j + 1))) atTop (𝓝 (contFrac a)) :=
    (tendsto_add_atTop_iff_nat (j + 1)).2 (tendsto_contConv ha)
  have T2 : Tendsto (fun n ↦ (contNum a (j + 1) + contNum a j * contConv s n : ℝ) /
      (contDen a (j + 1) + contDen a j * contConv s n)) atTop
      (𝓝 ((contNum a (j + 1) + contNum a j * contFrac s) /
        (contDen a (j + 1) + contDen a j * contFrac s))) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_contConv hs))).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_contConv hs))) hQ.ne')
  refine tendsto_nhds_unique (T1.congr fun n ↦ ?_) T2
  have hsn := contDen_pos_real hs n
  have hj1 := contDen_pos_real ha (j + 1)
  have hj := contDen_pos_real ha j
  have hp : (0 : ℝ) ≤ contNum s n := Nat.cast_nonneg _
  have hp' : (0 : ℝ) ≤ contNum a j := Nat.cast_nonneg _
  unfold contConv
  rw [show n + (j + 1) = j + 1 + n by ring, contNum_add, contDen_add, ← hsdef]
  push_cast
  have hD : (0 : ℝ) < contDen a (j + 1) * contDen s n + contDen a j * contNum s n := by positivity
  have hD' : (0 : ℝ) < contDen a (j + 1) + contDen a j * (contNum s n / contDen s n) := by
    positivity
  rw [div_eq_div_iff hD.ne' hD'.ne']
  field_simp

                                                                                               
                                                                            
                                      
                                                                        
                                                                             
                                                                             
                                                                                             
                        
                                                                                     
                                                                                               
                    
                                                                                               
             
                                             
                                                         
                                
                                                         
                             
                                     
                                           
                                                   
                                                         
                                         
                                             
                                                               
                                             
                                                                         
                                                   
                              
                              
           
                    
                                                                                     
                             

                                                                                                  
                           
                                                             
                                                                                     
         
                                                        
                                                              
                                                           
                                                                       
                                                                                          
                                                            
                                
                                                                      

                                                                                        
                                                                                   
                                                
                                                           
                                                                          
                              
                                                                
                                   
                     
                                                                                  
                                                                                      
                                                                                   
                                                                                   
                                                                                        
                                                   
                
                              
                                        
                       
                           

end Positive

end Nat
