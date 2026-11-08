/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib

/-! The two-particle kernel has a two-center integral representation with coefficient `4π` and center variance `(u-r)/2`. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

instance spectator_pairTwo_isEmpty : IsEmpty (Spectator pairTwo) := by
  refine ⟨fun i => ?_⟩
  have hi := i.1.isLt
  have h0 := i.2.1
  have h1 := i.2.2
  simp only [pairTwo] at h0 h1
  have h0' : i.1.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h1' : i.1.val ≠ 1 := fun h => h1 (Fin.ext h)
  omega

                                                                           
                                                                     
                                                     
          
                                                    

                                                                 
                                                                       
                           
                                                                                            
                                                                                       

                                                                
                                                                              
                                     
                                                                            
                                                                               

                                                                          
                                                                        
                                                                        
                                                                                  
               
                                                                                        
                        
                                                       
                                                              
                                                                            

                                                                                      
                                                               
                                            
                                                                                       
                                             
                                                                                        
                                                                      
                             
               
                                                  
                                                                    
                                                   
                                            
                                                                 
                                               

                                                                                      
                                                                                    
                                   
                                                                   
                                                                          
                                                               
                                             
                                                                                          
                                        
                       
         
                       
         
                                                                         
                                                  
                                            
                                                                      
                                                                                               
                                                                                
                                                 
                               
                     
            
                                                                                            
                                     
                                       

end Critical2DKPZ.DeltaBose
