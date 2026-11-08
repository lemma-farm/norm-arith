module

                                                       
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic

@[expose] public section

/-!
# Response moment elementary estimates

Small deterministic facts used by the resampling and comparison chain of
`mfd:sec-resampling`.

* the ramp `χ_{a,b}` of `mfd:sec-resampling` and its two endpoint values;
* `(x+y)^2 ≤ 2x^2 + 2y^2`, `mfd:sec-resampling`;
* the geometric sums used for the all-chain tail, `mfd:sec-resampling`;
* the Efron--Stein sum of `mfd:sec-resampling`.
-/

open Finset Filter Topology

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

                                                      
             
       

                                                      
             
       

                                                                                       
             
                                    
                                         
                      
            
                                                                               
                        

                                                                                        
                                     
                                      
                                      
                                           
             
                                                                 

                                                          
                                                       
                                         
                                                                                     
                                                                     
                                                                        
                                 
                                                                                      
                                                                       
          
                  
                                                                     
                                                     
                                                                                    
                                                                      
                                                       
          
                  
                                                                            
                        
                                                                               
                                     
                                
                                                                                      
                                                                       
                                                       
                                 

                                                                               
                               

                                                   
                                                                     
                                                      
                                    
                            
            
                                                
                                         
                    
           
                              
                                 
        
                                        

                                                         
                                               
                                                     
                                                               
                                                                       
                                                                       
                                     
                       
                                                                                 
           
                                                                  
                                              
      
                                             
                                                               
                          
                 
                       
                                                             
                            
                                                       
                    

                                                                  
                                                         
                                         
                                                         
                    
                                              
                                                      
                                                                
                                                    
                                                               
                                                    
                                                          
                                                                  
                                                              
                              
                                 
                                     
            
                                    
                        
                                                                           
                                                                       
                                   
                                                   
               
           
                        
                                                                           
                                                                 
                                   
                                             
               
           

                                                             
                                     
                                       
                                          
                                                          
                         
                                                       
                                                                        
                           
                                                                 

theorem efron_stein_square_sum_le {n : ℕ} (Del mx : ℝ) (_hDel : 0 ≤ Del)
    (nu ze : Fin n → ℝ) (hnu : ∀ i, 0 ≤ nu i) (hze : ∀ i, 0 ≤ ze i)
    (hmx : ∀ i, nu i ≤ mx) :
    (∑ i : Fin n, (Del * nu i + Real.sqrt (nu i * ze i)) ^ 2) ≤
      2 * Del ^ 2 * mx * (∑ i : Fin n, nu i) + 2 * mx * (∑ i : Fin n, ze i) := by
  have hterm : ∀ i : Fin n,
      (Del * nu i + Real.sqrt (nu i * ze i)) ^ 2 ≤
        2 * Del ^ 2 * mx * nu i + 2 * mx * ze i := by
    intro i
    have hnu_i : 0 ≤ nu i := hnu i
    have hze_i : 0 ≤ ze i := hze i
    have hsq : (Real.sqrt (nu i * ze i)) ^ 2 = nu i * ze i :=
      Real.sq_sqrt (mul_nonneg hnu_i hze_i)
    have hnu_le : nu i * nu i ≤ mx * nu i :=
      mul_le_mul_of_nonneg_right (hmx i) hnu_i
    have ha : (Del * nu i) ^ 2 ≤ Del ^ 2 * (mx * nu i) := by
      have h := mul_le_mul_of_nonneg_left hnu_le (sq_nonneg Del)
      nlinarith [h]
    have hb : (Real.sqrt (nu i * ze i)) ^ 2 ≤ mx * ze i := by
      rw [hsq]
      exact mul_le_mul_of_nonneg_right (hmx i) hze_i
    have h1 := two_mul_le_add_sq (Del * nu i) (Real.sqrt (nu i * ze i))
    nlinarith [h1, ha, hb]
  calc ∑ i : Fin n, (Del * nu i + Real.sqrt (nu i * ze i)) ^ 2
      ≤ ∑ i : Fin n, (2 * Del ^ 2 * mx * nu i + 2 * mx * ze i) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 2 * Del ^ 2 * mx * (∑ i : Fin n, nu i) + 2 * mx * (∑ i : Fin n, ze i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]


                                                                          
                                                                             
                                                                            
             
                               
                                                                    
                                                          
                          
                      
                                                                 
                
                  
                           
                                           
                                                                                      
           
                    
                            
                  
                                         
                                           
                    
                                                  
                                                                
                      
                                                                                      
                                                            
                                        
                                                                              
                                                             
                           
                    
              
                
                                                                 
           
                      
                                                        
             
                                                                         
          

end ResponseMoments
end SubdiffusiveProcess
