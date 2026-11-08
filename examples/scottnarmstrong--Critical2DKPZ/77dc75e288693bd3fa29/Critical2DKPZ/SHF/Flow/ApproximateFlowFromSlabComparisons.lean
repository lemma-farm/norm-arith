/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabMollifierConvergence
public import Critical2DKPZ.SHF.Flow.MomentKernelTwoSemigroup
public import Critical2DKPZ.SHF.Flow.ApproximateFlowIntegrability
import Mathlib

/-! # Approximate composition from three slab comparisons -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

private theorem sq_sub_le_three_sq_errors (a b c d : ℝ) :
    (a - d) ^ 2 ≤ 3 * ((a - b) ^ 2 + (b - c) ^ 2 + (d - c) ^ 2) := by
  nlinarith only [sq_nonneg ((a - b) - (b - c)),
    sq_nonneg ((a - b) + (d - c)), sq_nonneg ((b - c) + (d - c))]

                                                                               
            
                                                  
                                                                             
                                                       
                                                                                                    
                                                                
                                                                     
                                                                                                    
                                                                                                  
                                                                             
                                                       
                                                                                                    
                                                                               
                                                                                                             
                                                                                              
                                                                                                
                                          
                                                         
                                                                                            
                                                                     
                                                                                                         
                                                                       
                                                        
                                                                                                        
                                               
                                                                 
                                                                                              
                                                                                                         
            
                                       
                                                                                                                   
                                                                                                         
                              
                                      
                                          
                                             
                                             
                                                                    
                                                         
                                                                                    
                            
                                                                        
            
                                                                           
                                                                                                
                                             
                
                                                     
                                                            
                                                      
                                
                                                  
                                                                                
                                        
                                                                    
                                        
                                                                                 
                                                              
                                                
                                                         
                                                              
                                                       
                              
                                                                   
                                      
                                                       
                                                             
                                      
                                                                       
                                     
                                    
                                                              
                                    
                                                                  
                                    
                                              
                                                                       
                                                                 
                             
                                                                 
                             
                                                                 
                             
                                                             
                                                             
                                                               
                                                
      
                                                     
                                           
                                                                                      
                                             
                                                                                  
                                                  
                                             
                                                  
                             
             
                                                  
                                                                      
                                 
                        

end Critical2DKPZ.SHF.Flow
