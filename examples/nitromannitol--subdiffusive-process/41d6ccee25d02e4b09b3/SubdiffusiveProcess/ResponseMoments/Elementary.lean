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

                                                      
             
       

                                                      
             
       

                                                                                       
             
                                    
                                         
                      
            
                                                                               
                        

                                                                                        
                                     
                                      
                                      
                                           
             
                                                                 

                                                          
                                                       
                                         
                                                                                     
                                                                     
                                                                        
                                 
                                                                                      
                                                                       
          
                  
                                                                     
                                                     
                                                                                    
                                                                      
                                                       
          
                  
                                                                            
                        
                                                                               
                                     
                                
                                                                                      
                                                                       
                                                       
                                 

                                                                               
                               

                                                   
                                                                     
                                                      
                                    
                            
            
                                                
                                         
                    
           
                              
                                 
        
                                        

                                                         
                                               
                                                     
                                                               
                                                                       
                                                                       
                                     
                       
                                                                                 
           
                                                                  
                                              
      
                                             
                                                               
                          
                 
                       
                                                             
                            
                                                       
                    

theorem abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  have key : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v →
      Real.sqrt v - Real.sqrt u ≤ Real.sqrt (v - u) := by
    intro u v hu huv
    have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
    have hsum : 0 ≤ Real.sqrt u + Real.sqrt (v - u) :=
      add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg (v - u))
    have h1 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
    have h2 : Real.sqrt (v - u) ^ 2 = v - u := Real.sq_sqrt hvu
    have h3 : 0 ≤ Real.sqrt u * Real.sqrt (v - u) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle : Real.sqrt v ≤ Real.sqrt u + Real.sqrt (v - u) := by
      have h : v ≤ (Real.sqrt u + Real.sqrt (v - u)) ^ 2 := by
        nlinarith [h1, h2, h3]
      have := Real.sqrt_le_sqrt h
      rwa [Real.sqrt_sq hsum] at this
    linarith
  rcases le_total x y with hxy | hyx
  · have h := key hx hxy
    have e1 : |Real.sqrt x - Real.sqrt y| = Real.sqrt y - Real.sqrt x := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.sqrt_le_sqrt hxy))]; ring
    have e2 : |x - y| = y - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
    rw [e1, e2]
    exact h
  · have h := key hy hyx
    have e1 : |Real.sqrt x - Real.sqrt y| = Real.sqrt x - Real.sqrt y := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hyx))]
    have e2 : |x - y| = x - y := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [e1, e2]
    exact h

                                                             
                                     
                                       
                                          
                                                          
                         
                                                       
                                                                        
                           
                                                                 

                                                                        
                                                                   
                            
                                                               
                                                                                 
                           
                                                  
                                                     
           
                                  
                                  
                                                             
                                           
                                            
                                              
                                                            
                                                                
                   
                                                             
              
                                                    
                                                                       
                          
                                                              
                                                                 
                                              
                                                                                   
                                                                   


                                                                          
                                                                             
                                                                            
             
                               
                                                                    
                                                          
                          
                      
                                                                 
                
                  
                           
                                           
                                                                                      
           
                    
                            
                  
                                         
                                           
                    
                                                  
                                                                
                      
                                                                                      
                                                            
                                        
                                                                              
                                                             
                           
                    
              
                
                                                                 
           
                      
                                                        
             
                                                                         
          

end ResponseMoments
end SubdiffusiveProcess
