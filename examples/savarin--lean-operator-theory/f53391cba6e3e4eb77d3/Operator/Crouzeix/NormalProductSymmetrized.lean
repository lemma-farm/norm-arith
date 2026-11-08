/-
# Universal circle symmetrization implies the normal auxiliary product bound

For any operator, the sharp symmetrized estimate on every polynomial forces
an enclosing circle's center into the closed numerical range.  Indeed, if the
center were outside, an affine polynomial separator would have value one at
the center and norm at most `r < 1` on the closed numerical range.  Applying
symmetrization to its powers makes the functional-calculus term tend to zero
by the unconditional Crouzeix--Palencia bound, while the circle auxiliary
remains the identity, a contradiction.

The aligned-circle normal product theorem then supplies the literal sharp
auxiliary product estimate.

## Main declarations

* `circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  proves alignment over a compact nonempty convex control set directly from
  universal symmetrization.
* `circle_center_mem_of_isCompact_nonempty_convex_of_global_polynomial_bound_of_forall_symmetrized_bound`
  retains the earlier finite-calculus interface as a corollary.
* `circle_center_mem_closure_numericalRange_of_global_polynomial_bound_of_forall_symmetrized_bound`
  specializes that result to the closed numerical range.
* `circle_center_mem_closure_numericalRange_of_forall_symmetrized_bound`
  specializes direct center alignment to the closed numerical range.
* `norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound`
  gives a uniform power bound on the polynomial ideal vanishing at the circle
  center.
* `norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound`
  preserves the coupled operator/scalar cancellation for every shifted power.
* `norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound`
  gives the corresponding centered power bound for every polynomial.
* `spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound`
  derives the sharp centered spectral inclusion from those power bounds.
* `spectrum_aeval_subset_closedBall_eval_of_forall_symmetrized_bound`
  translates that inclusion back to the spectrum of `p(A)`.
* `spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound`
  gives the analogous sharp spectral disk around every scalar shift.
* `spectrum_aeval_subset_closedBall_shift_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  discharges center membership from compact convex geometry.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_mem_of_forall_symmetrized_bound`
  converts a shifted disk and center membership to a shifted spectral radius.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  gives the sharp spectral-radius bound after every scalar shift.
* `spectralRadius_aeval_le_polynomialSupNorm_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  records its zero-shift specialization.
* `spectrum_aeval_subset_closedBall_shift_closure_numericalRange_of_forall_symmetrized_bound`
  specializes every shifted disk to the closed numerical range.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_closure_numericalRange_of_forall_symmetrized_bound`
  gives the corresponding sharp shifted spectral-radius bound.
* `spectralRadius_aeval_le_polynomialSupNorm_closure_numericalRange_of_forall_symmetrized_bound`
  gives its zero-shift consequence.
* `spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  proves that the compact convex control set itself contains the spectrum.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul`
  proves the sharp product bound without normality when the center value is
  at most `sqrt 2 - 1` times the control norm.
* `norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound`
  extracts the operator-norm estimate obtained from any scalar shift.
* `isKPolynomialSpectralSet_three_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  packages universal symmetrization as a constant-three polynomial spectral set.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_shifted_scalar_bound_of_forall_symmetrized_bound`
  exposes an arbitrary scalar shift for optimizing the product estimate.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_half_centered_scalar_bound_of_forall_symmetrized_bound`
  specializes the shift to `p(c) / 2`, eliminating the residual scalar term.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound`
  isolates the exact adaptive scalar criterion obtained by centering `p`.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_polynomialSupNorm_le_sub_of_forall_symmetrized_bound`
  proves the complementary sharp near-constant branch.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_one_add_sqrt_two_mul_sq_of_forall_symmetrized_bound`
  gives the resulting product estimate for an arbitrary operator at the
  global Crouzeix--Palencia factor.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval_of_forall_symmetrized_bound`
  gives the sharp product estimate whenever the individual value `p(A)` is
  star-normal.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_of_forall_symmetrized_bound`
  specializes the sharp estimate to a star-normal operator.
-/
import Operator.Crouzeix.ConvexRunge
import Operator.Crouzeix.NormalProduct
import Operator.Crouzeix.SmoothSupportDomain
import Operator.NumericalRange.Convex
import Operator.NumericalRange.Nonempty
import Mathlib
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private theorem polynomialSupNorm_pow_le_of_isCompact
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) (n : ℕ) :
    polynomialSupNorm (p ^ n) K ≤ polynomialSupNorm p K ^ n := by
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_)
    (pow_nonneg (polynomialSupNorm_nonneg p K) n)
  refine Real.iSup_le (fun hz ↦ ?_)
    (pow_nonneg (polynomialSupNorm_nonneg p K) n)
  simp only [Polynomial.eval_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz) n

                                                                          
                                                                        
                                                                            
                                                                              
                                     
                                                                                  
                                              
                                                                            
                   
                                        
                                
                             
                                                     
                                        
                                                            
                                    
               
              
                                      
                                                            
                                     
                                                   
                                             
                               
                                           
                                                 
                              
                                                       
                                                        
                                             
                                                       
                                                 
                                  
                                                    
                           
                                                                               
               
                                                                        
                                                      
                     
                          
                                                                
                                                                
                            
                                                  
                                                   
                                             
                                          
                                        
                                                                            
                                                    
                                  
                                                          
                           
                                                                               
                     
                                                                        
                                                                  
                           
                             
                                 
                                                               
                                                          
        
                             
                                                     
                   
                  
                                 
                                                        
                             
                                
                
                   
                                        
                                           
                
          
                       
                                 
                                                           
                                                         
                              
              
                        
                                 
                                                        
               
                                 
                                                         
                                                             
                            
                                                              
                                             
                                            

                                                                        
                                                                              
                                                                         
                                                     
       
                                                                                                         
                                              
                                                                            
                   
                                        
                         
                                 
                                                         
                                
                             
                                                     
                                        
                                                            
                                    
               
       
                                                                              
                                             

                                                                            
                                                                        
                                                                       
                      
       
                                                                                                   
                                                  
                                        
                         
                                 
                              
                                                             
                                
                             
                                                     
                                        
                                                            
                                                               
                                        
       
                                                                              
                                                      
                                                                            
                                                    

                                                                           
                                                            
                                                                            
                                                  
                                        
                                
                             
                                                     
                                        
                                                            
                                                               
                                        
       
                                                                              
                                                      
                                                                            
                                                    

                                                                           
                                                                             
                                                                     
                                                                  
       
                                                                                               
                                   
                                        
                                  
                                
                             
                                                     
                                        
                                                            
                                  
                                                                
                                      
                                               
                                  
                                                                             
                                 
                                               
                                                                          
                                             
                                                                         

                                                                          
                                                                        
                                                                           
                                            
theorem
    norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) (n : ℕ) :
    ‖(Polynomial.aeval A p - b • (1 : E →L[ℂ] E)) ^ (n + 1) +
        (Polynomial.eval c p - b) ^ (n + 1) •
          (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm (p - Polynomial.C b) K ^ (n + 1) := by
  let q : Polynomial ℂ := p - Polynomial.C b
  have hpow := hsymm (q ^ (n + 1))
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA (q ^ (n + 1)), star_smul, star_one, star_star] at hpow
  have hbound := hpow.trans (mul_le_mul_of_nonneg_left
    (polynomialSupNorm_pow_le_of_isCompact q hK (n + 1)) (by positivity))
  simpa only [q, map_pow, map_sub, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_C] using hbound

                                                                       
                                                                  
                                                                         
                                                 
       
                                                                                                       
                                   
                                        
                                  
                                
                             
                                                     
                                        
                                                            
                                  
                                
                            
                                                           
                           
                                                                  
              
                                                                                                                     
                                               
                                                                 
                        

                                                                      
                                                                         
                                                             
                                                                         
            
       
                                                                                  
                                   
                                        
                                  
                                
                             
                                                     
                                        
                                                            
                                  
                        
                                      
                                                
                         
                                                                            
                                                  
               
                                 
                            
             
                                             
                                         
                                
                                              
            
                                             
               
                                                 
                                        
                                         
                                                            
                                                              
                                                          
                                                       
                                                      
                                                        
                                                              
                   
                                                                             
                                  
                                                            
                                     
                                                     
                                                                      
                                                    
                           
                                                                                                         
                           
                                                      
        
                       
                                                         
                        
                      
                              
                                                                   
                                    
                                                     

                                                                          
                                                 
                                                     
                                                                         
                                   
                                        
                                  
                                
                             
                                                     
                                        
                                                            
                                  
                        
                                       
                                             
                                                                            
                   
                                                                                  
                       
                                                  
                                              
                                         
                                             
                                                                      
            
                                             
                                        
                                                    
               
                                                                
                                     
                                                       
                                           

                                                                        
                                                                             
                                                                         
                                                                        
                                                  
theorem spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K) (hc : c ∈ K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall b (polynomialSupNorm (p - Polynomial.C b) K) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let _ := hE
  let T : E →L[ℂ] E := Polynomial.aeval A p -
    b • (1 : E →L[ℂ] E)
  let a : ℂ := Polynomial.eval c p - b
  let m : ℝ := polynomialSupNorm (p - Polynomial.C b) K
  have ha : ‖a‖ ≤ m := by
    have h := norm_eval_le_polynomialSupNorm (p - Polynomial.C b)
      (bddAbove_norm_eval_image_of_isCompact (p - Polynomial.C b) hK) hc
    simpa only [a, m, Polynomial.eval_sub, Polynomial.eval_C] using h
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  let w : ℂ := z - b
  have hw : w ∈ spectrum ℂ T := by
    have hshift : spectrum ℂ T =
        spectrum ℂ (Polynomial.aeval A p) - ({b} : Set ℂ) := by
      dsimp only [T]
      rw [← Algebra.algebraMap_eq_smul_one,
        ← spectrum.sub_singleton_eq]
    rw [hshift]
    exact ⟨z, hz, b, Set.mem_singleton b, rfl⟩
  by_contra hwm
  have hm : 0 ≤ m := polynomialSupNorm_nonneg _ _
  have hmw : m < ‖w‖ := lt_of_not_ge hwm
  have hwpos : 0 < ‖w‖ := hm.trans_lt hmw
  have hratio_nonneg : 0 ≤ m / ‖w‖ := div_nonneg hm hwpos.le
  have hratio_lt_one : m / ‖w‖ < 1 := (div_lt_one hwpos).2 hmw
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (m / ‖w‖) ^ n < (1 / 3 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hratio_lt_one
  have hratio_succ : 3 * (m / ‖w‖) ^ (n + 1) < 1 := by
    have hratio_le_one : m / ‖w‖ ≤ 1 := hratio_lt_one.le
    have hpow_succ : (m / ‖w‖) ^ (n + 1) ≤ (m / ‖w‖) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hratio_nonneg n) hratio_le_one
    nlinarith only [hn, hpow_succ]
  have hwpow_mem : w ^ (n + 1) ∈ spectrum ℂ (T ^ (n + 1)) :=
    spectrum.pow_mem_pow T (n + 1) hw
  have hadd_mem : w ^ (n + 1) + a ^ (n + 1) ∈
      spectrum ℂ (T ^ (n + 1) +
        a ^ (n + 1) • (1 : E →L[ℂ] E)) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq]
    exact ⟨w ^ (n + 1), hwpow_mem, a ^ (n + 1),
      Set.mem_singleton _, rfl⟩
  have hadd_le : ‖w ^ (n + 1) + a ^ (n + 1)‖ ≤
      ‖T ^ (n + 1) + a ^ (n + 1) • (1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_of_mem hadd_mem
  have hmoment : ‖T ^ (n + 1) +
      a ^ (n + 1) • (1 : E →L[ℂ] E)‖ ≤ 2 * m ^ (n + 1) := by
    simpa only [T, a, m] using
      norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
        A c hA hK hsymm p b n
  have hapow : ‖a‖ ^ (n + 1) ≤ m ^ (n + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ha (n + 1)
  have hwpow_le : ‖w‖ ^ (n + 1) ≤ 3 * m ^ (n + 1) := by
    calc
      ‖w‖ ^ (n + 1) = ‖w ^ (n + 1)‖ := (norm_pow w (n + 1)).symm
      _ = ‖(w ^ (n + 1) + a ^ (n + 1)) - a ^ (n + 1)‖ := by
        rw [add_sub_cancel_right]
      _ ≤ ‖w ^ (n + 1) + a ^ (n + 1)‖ + ‖a ^ (n + 1)‖ :=
        norm_sub_le _ _
      _ ≤ 2 * m ^ (n + 1) + m ^ (n + 1) := by
        simpa only [norm_pow] using add_le_add (hadd_le.trans hmoment) hapow
      _ = 3 * m ^ (n + 1) := by ring
  have hstrict : 3 * m ^ (n + 1) < ‖w‖ ^ (n + 1) := by
    calc
      3 * m ^ (n + 1) =
          (3 * (m / ‖w‖) ^ (n + 1)) * ‖w‖ ^ (n + 1) := by
            rw [div_pow]
            field_simp
      _ < 1 * ‖w‖ ^ (n + 1) :=
        mul_lt_mul_of_pos_right hratio_succ (pow_pos hwpos (n + 1))
      _ = ‖w‖ ^ (n + 1) := one_mul _
  exact (not_lt_of_ge hwpow_le) hstrict

                                                                             
                                                                         
                
       
                                                                                                   
                                   
                                        
                                               
                                
                             
                                                     
                                        
                                                            
                                  
                                
                    
                                                      
                                                                           
                                                           
                                
                          
                                                    
                                                             
                                                                      
                                
                   
                                    
                                   
          
                
                                                                             
                               
                                                    
                                                          
                           
              

                                                              
                                                                           
                                                                            
       
                                                                                                   
                               
                                                                            
                   
                                        
                                
                             
                                                     
                                        
                                                            
                                  
                                
                                       
                                                                          
                                                  
               
                                 
                            
             
       
                                                                             
                     
                                                                                   
                                                  
                 

                                                                              
                                                                           
       
                                                                                                                         
                               
                                                                            
                   
                                        
                                
                             
                                                     
                                        
                                                            
                                  
                                
                    
                                                      
                                                                           
                                                  
               
                                                           
                                   
                
             
       
                                                                                                   
                     
                                                                                   
                                                  
                 

                                                                              
                                                                            
                                                                        
         
       
                                                                                                      
                               
                                                                            
                   
                                        
                                
                             
                                                     
                                        
                                                            
                                  
                        
                                             
                                                        
                                                        
                                                                                                                         
                                                 

                                                                            
                                                                
                                                                         
       
                                                                                             
                                   
                                        
                                
                             
                                                     
                                        
                                                            
                                                             
                                
                                       
                         
                                               
                                             
                                                  
               
                                 
                            
             
       
                                                                                                   
                                                      
                                                                            
                                                        

                                                                            
                                                                           
       
                                                                                                                   
                                   
                                        
                                
                             
                                                     
                                        
                                                            
                                                             
                                
                    
                                                      
                                              
                                                               
                                                      
                                                                  
                          
                                                    
                                                             
                                                                      
                                
                   
                                    
                                   
          
                
                                                                                             
                         
                                                    
                                                          
                           
              

                                                                            
                                                                            
                                       
       
                                                                                                
                                   
                                        
                                
                             
                                                     
                                        
                                                            
                                                             
                        
                                             
                                                                                   
                                                        
                                                                                                                   
                      

                                                                           
                                                                         
                                                                        
                                                                         
                                                                        
              
                                                                                
                               
                                                                            
                   
                                        
                                
                             
                                                     
                                        
                                                            
                                    
                          
                                                  
               
                                 
                            
             
            
               
                                      
                                                            
                                      
                                             
                            
                                        
                                              
                                      
                                             
                                      
                      
                 
                                                                                                   
                                                         
                                                        
                                             
                                                                      
                                            

                                                                            
                                                                     
                                                                              
                                                                              
       
                                                                                                            
                                   
                                        
                                  
            
                             
                                                     
                                        
                                                            
                                  
                                     
                                                  
                           
                                             
                                      
                                                         
                                     
                                                  
               
                                       
                                             
                                      
                                                             
                           
                         
                     
             
                                    
                                    
                                                 
                                  
                                                                  
                                                                   
                          
                    
                                                                             
                                                     
                                                     
        
                              
                                  
                                                    
                                                          
                                     
                                 
                                                    
                                                                    
                         
                                         
                                                           
                            
                                        
                                                                  
                                                       
                                
                                              
        
                                                    
                                           
                                                                   
                                                                            
                                      
                                                                             
             
      
                           
                                                         
                                
                                                           
                     
                                        
                                                  
                                                            
                        

                                                                        
                                                                     
                                                                     
       
                                                                                                       
                                   
                                        
               
                                
                             
                                                     
                                        
                                                            
                                  
                                
                            
                                                    
                                           
                                                  
               
                                                                  
                         
                    
                                                               
                     
             
                                            
                                    
                                            
                      
                                                                             
                                                     
                                      
                                                          
                             
                                       
                             
                                                  
                                                             
                                              
                                                          
                                                     
        
      
                            
                                
                                                    
                                         
                                                     
                               
                                                    
                                          
                                               
                       
                                       
                                        

                                                                           
                                                                             
                                                                        
                                                                             
                                  
       
                                                                                           
                               
                                                                            
                   
                                        
                                
                             
                                                     
                                        
                                                            
                                    
                                        
                                                  
               
                   
                                   
                              
             
                                                                    
                           
                                                                   
             
          
                                                                            
                                                  
                    
                                                                              
                                             
         
                                    
             
                                                                                                       
                      
                                         
                                    
                                                           
      
                                                                
                                                                  
                                                     
                                            

                                                                 
                                                                       
                                                                   
                                                                    
       
                                                                                                                         
                                   
                                        
               
                                
                             
                                                     
                                        
                                                            
                                  
                              
              
                                                     
                                                                
                                  
                           
                                             
                                      
                                                         
                                     
                                                  
               
                                       
                                             
                                      
                                                             
                           
                         
                     
             
                                    
                                    
                                  
                                     
                                                    
                                        
                                                                                                       
                      
                                                                             
             
      
                           
                                                         
                                
                                                           
                     
                                        
                                                  
                                                       
                                               
                                       
                        

                                                                           
                                                             
                                                                     
       
                                                                                                                               
                                   
                                        
               
                                
                             
                                                     
                                        
                                                            
                                  
                      
              
                           
                                                          
                                                            
                           
                                             
                                      
                                                         
                                     
       
                                                                                                                         
                                              
                                                                            
        
                                                       

                                                                   
                                                                           
                                                                          
                                   
       
                                                                                                                          
                                   
                                        
               
                                
                             
                                                     
                                        
                                                            
                                  
                      
              
                            
                                                      
                                                        
                                  
                           
                                             
                                      
                                                         
                                     
       
                                                                                                                         
                                          
                                                                
                                 
                                                            
                                             
                                  

                                                                         
                                                               
                                                                            
                                                                              
       
                                                                                                                                      
                                   
                                        
               
                                
                             
                                                     
                                        
                                                            
                                  
                      
                                  
                                                    
                                                      
                           
                                             
                                      
                                                         
                                     
                                    
                                    
                                                                
                                    
                                  
       
                                                                                                                          
                    
                                    
                                    
                                                
                                               
      
                                              
                                                                 
                                  
                                            

                                                                             
                                                         
                                                                              
                                                                        
                                                                          
       
                                                                                                                         
                                   
                                        
                                
                             
                                                     
                                        
                                                            
                                                             
                        
                           
                                             
                                      
                                                         
                         
                                                                  
                                                  
               
                                       
                                             
                                      
                                                             
                           
                         
                                                                                
             
                                                               
                                                           
                                                  
                                             
                                                                        
                  
                                                              
                             
                                         
                                    
                                                           
                                                                             
             
      
                           
                                                         
                                
                                                           
                     
                                                            
                                                  
                                      
                                        
                                   
                           
                                                                  
                            
          

                                                                             
                                                                         
                                                                        
       
                                                                                                                       
                                   
                                        
                                
                             
                                                     
                                        
                                                            
                                                             
                                                              
                           
                                             
                                      
                                                         
                                                                
                                                  
               
                                       
                                             
                                      
                                                             
                           
                         
                     
             
       
                                                                                           
            
       
                                                                        
                  

                                                                             
                                                                                 
       
                                                                                                                 
                                                    
                                        
                                
                             
                                                     
                                        
                                                            
                                                             
                        
                           
                                             
                                      
                                                         
                                                                
                                                          
                             
                           
                  
       
                                                                                                                       
                    
