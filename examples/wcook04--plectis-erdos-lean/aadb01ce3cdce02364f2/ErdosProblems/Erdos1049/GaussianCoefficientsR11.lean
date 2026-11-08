import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import Mathlib

/-! # Coefficient bounds for the actual Gaussian recurrence

This is a supplier for Gaussian factors, not an assertion of a bound on a
cancelled rational coefficient that has not yet been identified as a polynomial.
-/
namespace ErdosProblems.Erdos1049.PaperR11
open Polynomial

/-- Coefficientwise positivity and the exact ordinary-binomial majorant. -/
theorem gaussian_coefficient_bounds (n k d : ℕ) :
    0 ≤ (gaussBinom (X : ℤ[X]) n k).coeff d ∧
    (gaussBinom (X : ℤ[X]) n k).coeff d ≤ (n.choose k : ℤ) := by
  induction n generalizing k d with
  | zero =>
      cases k with
      | zero =>
          by_cases hd : d = 0 <;> simp [gaussBinom, coeff_one, hd]
      | succ k => simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero =>
          simp only [gaussBinom_zero_right, Nat.choose_zero_right]
          by_cases hd : d = 0
          · subst d; norm_num
          · simp [coeff_one, hd]
      | succ k =>
          by_cases hk : k ≤ n
          · rw [gaussBinom_succ, if_pos hk, coeff_add, coeff_X_pow_mul']
            by_cases hd : n - k ≤ d
            · rw [if_pos hd]
              obtain ⟨ha, hA⟩ := ih (k + 1) d
              obtain ⟨hb, hB⟩ := ih k (d - (n - k))
              constructor
              · exact add_nonneg ha hb
              · rw [Nat.choose_succ_succ, Nat.cast_add]
                linarith
            · rw [if_neg hd, add_zero]
              obtain ⟨ha, hA⟩ := ih (k + 1) d
              refine ⟨ha, ?_⟩
              rw [Nat.choose_succ_succ, Nat.cast_add]
              have hb : (0 : ℤ) ≤ n.choose k := by positivity
              linarith
          · have hnk : n < k + 1 := by omega
            rw [gaussBinom_succ, if_neg hk,
              gaussBinom_eq_zero_of_lt (X : ℤ[X]) hnk, add_zero, coeff_zero]
            exact ⟨le_rfl, by positivity⟩

lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
      cases k with
      | zero =>
          have h := ih 0
          simp only [Nat.choose_zero_right] at h ⊢
          rw [pow_succ]
          nlinarith [Nat.zero_le (2 ^ n)]
      | succ k =>
          rw [Nat.choose_succ_succ, pow_succ]
          have h1 := ih k
          have h2 := ih (k + 1)
          calc
            n.choose k + n.choose (k + 1) ≤ 2 ^ n + 2 ^ n := Nat.add_le_add h1 h2
            _ = 2 ^ n * 2 := by omega

                                                                    
                                                 
                                                             
                                                         
                         
                                                           

                                                                                    
                                                                     
                                                             
                            
                                                             
                                
             
                                                                         
                                                                  
                                                             

                                                                           
                                                             
                                                                               
                                                                        

end ErdosProblems.Erdos1049.PaperR11
