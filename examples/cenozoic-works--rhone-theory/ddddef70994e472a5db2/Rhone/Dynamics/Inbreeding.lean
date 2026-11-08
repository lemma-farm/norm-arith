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

                                                          
                        

                                                                             
             
           
                                  
                                  
                          
                                              
                                                
              
                        

                                    
                                                                     
                                                   
                                                         
                                                          
                               
                                            

                                       
theorem full_sib_deficit_recursion (z : ℝ × ℝ) :
    1 - (fullSibStep z).2 = (1 - z.2) / 2 + (1 - z.1) / 4 := by
  unfold fullSibStep
  ring

                                       
                                                                                
                        

                                       
                                                                                  
                                                      

private noncomputable def sibError (z : ℝ × ℝ) : ℝ := |1 - z.1| + 2 * |1 - z.2|

private theorem sibError_step (z : ℝ × ℝ) : sibError (fullSibStep z) ≤ sibError z := by
  have h := abs_add_le ((1 - z.2) / 2) ((1 - z.1) / 4)
  rw [abs_div, abs_div] at h
  norm_num at h
  have he := full_sib_deficit_recursion z
  unfold sibError
  change |1 - z.2| + 2 * |1 - (fullSibStep z).2| ≤ _
  rw [he]
  linarith [abs_nonneg (1 - z.1)]

                                                
                                                                           
                                                     
                                                                  
                                                      
                                                                  
                                                       
                                                       
                                
                   
                 
                      
                                 

                                                      
                                                                             
                                             
                
                                      
                  
                                                 
                                                                                 
        
                                                                  
                                                                              
                                                                  
                                                        
                      

                                       
                                      
                                                     
                                                
                                                                                 
                                             
                                                                 
         
                                                        
                                                                                         
                  
                                
                                                                          
                                    
                                                                       
                                                                    
                                                                 
                                       
                                             
                                
                                                                           
                                          
                       
                                                     
                                                            
                                                                 
                                       
                                             
                                
                                                                           
                                          
                       
                                                     
                                                           
                                                           
                 
                         

end Rhone.Dynamics.Inbreeding
