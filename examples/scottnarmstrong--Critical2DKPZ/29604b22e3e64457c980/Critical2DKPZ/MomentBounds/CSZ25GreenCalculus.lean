/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Green
import Critical2DKPZ.Polymer.SummableCovariance
import Critical2DKPZ.Lattice.Basic

/-! # Summability and finite-time calculus of Green energies -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- The truncated Green function is nonnegative. -/
theorem truncatedGreen_nonneg (L : ℕ) (z : Site) : 0 ≤ truncatedGreen L z :=
  Finset.sum_nonneg fun n _ => srwKernel_nonneg (2 * n) z

                                                                   
                                                                           
      
                                         
                                                                     
                    

                                                                                  
                                                     
                                                      
                                                                     
                                
                                                             
                                                              
      
                                                    
                                                                                    
                    

                                                                                     
                                                                             
                         
                                                                                     
                                                                                          
                                                                                         

                                                                     
                                                                                
                         
                                                                                      
                                                                                           
                                                 
                                                         

                                       
                                                                       
                          
                                           
                                                                     

                                                    
                                                                                   
                         
                                           
                                                   
                                                   
                                      
         
                                                            
         
                                           
                                          
                                                                               
                                       

                                                                    
                                                                     
                         
                                                       
                                                 
                                   
                                          
                                                       
                                              
                                                                          
                                                                                                  
                  
                                                                                             

end Critical2DKPZ.MomentBounds
