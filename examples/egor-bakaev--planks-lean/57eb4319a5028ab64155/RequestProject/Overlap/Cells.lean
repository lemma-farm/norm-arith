module

public import RequestProject.Overlap.Hull
public import Mathlib
/-!
# Cells of the final hole, greedy selection, and auxiliary plane geometry

* The final hole of a family of surviving planks `S` is partitioned by sign patterns
  `A ⊆ S` into the convex open *cells* `cell P S A`.
* An abstract greedy (Vitali-type) selection of pairwise disjoint sets.
* Small facts on coordinates and on crossing points of center lines.
-/

@[expose] public section

open MeasureTheory Set Metric Real
open scoped ENNReal

noncomputable section

namespace Annulus

/-! ### Plane geometry -/

/-- Decomposition of an inner product in the frame `(n, Jn)`. -/
lemma inner_decomp {n : Plane} (hn : ‖n‖ = 1) (x q : Plane) :
    inner ℝ x q = inner ℝ x n * inner ℝ n q + inner ℝ x (J n) * inner ℝ (J n) q := by
  conv_lhs => rw [decomp_frame hn x]
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]

                                                                      
                                                                 
                     
                                                                             
                          
                                                       
                                                

                                                                                            
                                                                   

                                                                        
                             
                                                               

namespace Plank

/-- A point close to two nonparallel center lines is close to their crossing point. -/
lemma norm_sub_crossPt_le {P Q : Plank} (h : P.ang Q ≠ 0) {x : Plane} {δ : ℝ}
    (hP : |inner ℝ x P.n - P.mid| ≤ δ) (hQ : |inner ℝ x Q.n - Q.mid| ≤ δ) :
    ‖x - P.crossPt Q‖ ≤ δ + 2 * δ / |inner ℝ (J P.n) Q.n| := by
  have hs := P.sin_ang_pos h
  set c := P.crossPt Q
  set d := x - c
  have hdP : inner ℝ d P.n = inner ℝ x P.n - P.mid := by
    rw [inner_sub_left, mem_centerLine.1 (crossPt_mem_left P Q)]
  have hdQ : inner ℝ d Q.n = inner ℝ x Q.n - Q.mid := by
    rw [inner_sub_left, mem_centerLine.1 (crossPt_mem_right h)]
  have hdec := inner_decomp P.norm_n d Q.n
  have hc : |inner ℝ P.n Q.n| ≤ 1 := P.abs_inner_n_le Q
  have h1 : |inner ℝ d (J P.n)| * |inner ℝ (J P.n) Q.n| ≤ 2 * δ := by
    rw [← abs_mul]
    have : inner ℝ d (J P.n) * inner ℝ (J P.n) Q.n =
        inner ℝ d Q.n - inner ℝ d P.n * inner ℝ P.n Q.n := by linarith
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, hdP, hdQ]
    have : |inner ℝ x P.n - P.mid| * |inner ℝ P.n Q.n| ≤ δ := by
      calc _ ≤ |inner ℝ x P.n - P.mid| * 1 := by gcongr
        _ ≤ δ := by linarith
    linarith
  have h2 : |inner ℝ d (J P.n)| ≤ 2 * δ / |inner ℝ (J P.n) Q.n| := by
    rw [le_div_iff₀ hs]; exact h1
  have h3 : ‖d‖ ≤ |inner ℝ d P.n| + |inner ℝ d (J P.n)| := by
    conv_lhs => rw [decomp_frame P.norm_n d]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, P.norm_n, norm_J, P.norm_n, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs]
  rw [hdP] at h3
  linarith

end Plank

                

                                

                                                       
                                                                                         

                                                                                           
                       
                                                        
                                                                 
                                          

                   
                                                                                
                            
                               
                                                         
                                                                                             
                     
                                  
                                
                                
                                                         
                                   
                                                                                    
                                        
              
                                
                                
                                                         
                                   
                                                                                    
                                        
              

                   
                                                                                            
                                                      
                                                                                               
                      
           
                                                                
                                                  
                                                            
                                                     
                     
                                                                            
                                              
                                                                            
                                              

                   
                                                                                       
            
                                       
                                    
                
                
                                               
                      
                                              
                                              

                   
                                                         
                                                  
           
            
                         
                                           
                        
                                                                              
                                                                                                    
                                     
                                               
                                                                         
                                
                           

                   
                                                            
                                                                    
                     
                                        
                 
                                                                                             
                                              
                                                        
                          
                      
                                                              
                                       
                                       
            
                          
                                                                            
                                       
                                       
            

                           

                                                                                         
                                      
                                                                                
                                              
                                                                        
           
                                                                         
             
                                              
                                           
                                                    
                                                            
                                
             
                                                                
                                                   
                                                         
                                  
              
                                               
               
                                                                          
                          
                                          
                                                
              
                        
                                                                         
                                         
                                                                                     
                                               
                                                      
                                                                   
                                                       
                          

end Annulus

end
