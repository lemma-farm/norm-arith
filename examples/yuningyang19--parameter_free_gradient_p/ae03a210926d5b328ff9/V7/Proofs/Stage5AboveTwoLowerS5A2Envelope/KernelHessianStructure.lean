import V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.ConditionalSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AGlobalC2

                                                                     
                                                                   
                                                   
                                                           
                               
                                              
                                                    
                                        
                                          
                                         
                                                      
                                                        
                                                  
                                                                       
                             

                                                                           
                                                                       
                                                             
                                                  
                                                           
                             
                                                      
                     
                                                                             
                                 
                                            
                                        
                                                 
                                              
                                                  
                                     
                              
                                                                       
                                           
                                                                
                                                      
                                                                            
                                  
                                               
                                         
                                                 
                 
                                                  
                                             
            
                              
                                          
                   
                    
                                    
                                                        
                                              
                                          
                                                                 
                                                               
                         
                                                                    
                                       
                                                            
                       
                                                   
                                                         
                                                                       
                     
                                                  
                          
                                  

/-- Cauchy--Schwarz for a symmetric positive-semidefinite Hessian form.  This
is the local algebraic wheel needed to retain the exact Banach-space constant
without passing through the ambient Euclidean operator norm. -/
lemma psd_pairing_cauchy_schwarz (H : Point d →L[ℝ] Point d)
    (hsymm : ∀ e f, O3.pairing e (H f) = O3.pairing f (H e))
    (hpos : ∀ e, 0 ≤ O3.pairing e (H e)) (e f : Point d) :
    O3.pairing e (H f) ^ (2 : ℕ) ≤
      O3.pairing e (H e) * O3.pairing f (H f) := by
  let A : ℝ := O3.pairing e (H e)
  let C : ℝ := O3.pairing f (H f)
  let X : ℝ := O3.pairing e (H f)
  have hA : 0 ≤ A := hpos e
  have hC : 0 ≤ C := hpos f
  have hquad (u v : Point d) (t : ℝ) :
      O3.pairing (u + t • v) (H (u + t • v)) =
        O3.pairing u (H u) +
          t * O3.pairing u (H v) +
          t * O3.pairing v (H u) +
          t ^ (2 : ℕ) * O3.pairing v (H v) := by
    simp only [map_add, map_smul, O3.pairing, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rcases hA.eq_or_lt with hAzero | hApos
  · rcases hC.eq_or_lt with hCzero | hCpos
    · have hplus := hpos (e + f)
      have hminus := hpos (e - f)
      have hp : O3.pairing (e + f) (H (e + f)) =
          O3.pairing e (H e) + O3.pairing e (H f) +
            O3.pairing f (H e) + O3.pairing f (H f) := by
        simpa using hquad e f 1
      have hm : O3.pairing (e - f) (H (e - f)) =
          O3.pairing e (H e) - O3.pairing e (H f) -
            O3.pairing f (H e) + O3.pairing f (H f) := by
        have h := hquad e (-f) 1
        simpa [sub_eq_add_neg, O3.pairing, hsymm] using h
      have hsym := hsymm e f
      dsimp [A, C, X] at hAzero hCzero ⊢
      rw [hp] at hplus
      rw [hm] at hminus
      nlinarith
    · let t : ℝ := -(X / C)
      have hz := hpos (e + t • f)
      rw [hquad] at hz
      have hsym := hsymm e f
      have hform : O3.pairing e (H e) +
            t * O3.pairing e (H f) +
            t * O3.pairing f (H e) +
            t ^ (2 : ℕ) * O3.pairing f (H f) =
          A - X ^ (2 : ℕ) / C := by
        dsimp [A, C, X, t]
        rw [hsym]
        field_simp [hCpos.ne']
        ring
      rw [hform] at hz
      have hdiv : X ^ (2 : ℕ) / C ≤ A := by linarith
      have hm := (div_le_iff₀ hCpos).mp hdiv
      dsimp [A, C, X] at hm ⊢
      nlinarith
  · let t : ℝ := -(X / A)
    have hz := hpos (f + t • e)
    rw [hquad] at hz
    have hsym := hsymm e f
    have hform : O3.pairing f (H f) +
          t * O3.pairing f (H e) +
          t * O3.pairing e (H f) +
          t ^ (2 : ℕ) * O3.pairing e (H e) =
        C - X ^ (2 : ℕ) / A := by
      dsimp [A, C, X, t]
      rw [← hsym]
      field_simp [hApos.ne']
      ring
    rw [hform] at hz
    have hdiv : X ^ (2 : ℕ) / A ≤ C := by linarith
    have hm := (div_le_iff₀ hApos).mp hdiv
    dsimp [A, C, X] at hm ⊢
    nlinarith

                                                                 
                                                
                                                           
                               
                                                        
                                                
                                                      
                                                            
                                                     
                                                        

end V7.Stage5AboveTwoLowerS5A2Envelope
