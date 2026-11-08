/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Exact partial-selfing recurrence -/

@[expose] public section

namespace Rhone.Dynamics.Inbreeding

                                                                     

                                                                

                                                        
                                                                              
                                               
            
      

                                                        
                      
                                                             
                                                    
                  
                
                
                                         
                                         
                                       
                 
                    

                                         
                                                             
                                                                 
                           
             
              
                                         
                                            
                     

                                       
                                          
                                                                 
                                                       
                                    
                                       
                                     
                                                            
                                                                      
                           
                                                                             

                                  
                                          
                                                                
                                                            
                                         
      

                                  
                                  
                                                                 
                                     
                                                                                     
                                                                                        

                                       
noncomputable def fullSibStep (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, (1 + 2 * z.2 + z.1) / 4)

                                                          
                        

                                                                             
             
           
                                  
                                  
                          
                                              
                                                
              
                        

                                    
                                                                     
                                                   
                                                         
                                                          
                               
                                            

                                       
                                                
                                                               
                    
      

                                       
                                                                                
                        

                                       
                                                                                  
                                                      

private noncomputable def sibError (z : ℝ × ℝ) : ℝ := |1 - z.1| + 2 * |1 - z.2|

                                                                                       
                                                      
                            
               
                                         
                 
                                                    
         
                                 

private theorem sibError_two_steps (z : ℝ × ℝ) :
    sibError (fullSibStep (fullSibStep z)) ≤ (3 / 4 : ℝ) * sibError z := by
  have hfirst : 1 - (fullSibStep (fullSibStep z)).1 =
      (1 - z.1) / 4 + (1 - z.2) / 2 := by simp [fullSibStep]; ring
  have hsecond : 1 - (fullSibStep (fullSibStep z)).2 =
      (1 - z.1) / 8 + (1 - z.2) / 2 := by simp [fullSibStep]; ring
  have h1 := abs_add_le ((1 - z.1) / 4) ((1 - z.2) / 2)
  have h2 := abs_add_le ((1 - z.1) / 8) ((1 - z.2) / 2)
  rw [abs_div, abs_div] at h1 h2
  norm_num at h1 h2
  unfold sibError
  rw [hfirst, hsecond]
  linarith [abs_nonneg (1 - z.1)]

                                                      
                                                                             
                                             
                
                                      
                  
                                                 
                                                                                 
        
                                                                  
                                                                              
                                                                  
                                                        
                      

                                       
                                      
                                                     
                                                
                                                                                 
                                             
                                                                 
         
                                                        
                                                                                         
                  
                                
                                                                          
                                    
                                                                       
                                                                    
                                                                 
                                       
                                             
                                
                                                                           
                                          
                       
                                                     
                                                            
                                                                 
                                       
                                             
                                
                                                                           
                                          
                       
                                                     
                                                           
                                                           
                 
                         

end Rhone.Dynamics.Inbreeding
