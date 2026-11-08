-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Flow.LinearGlobalExistence
public import Mathlib

/-! Grönwall bounds for global linear flows with coefficients bounded only on
the finite time window under consideration. -/

@[expose] public section

open Set
open scoped Topology

namespace AVenhance.Infra.Flow

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {V : ℝ → E → ℝ → E}

                                                        
                                        
                                                             
                                         
                                                       
         
                                                            
                                                   
                                                      
                             
                          
                                
                                                                      
                                           
                                               
                                          
                                           
        
                                                              
                                                     
                                                        
                       
                                                          
                                                  
                                                                             
                   
      
                                                  
                                        
                                                    

                                                                         
                                                                          
          
                                       
                                        
                                    
                                       
             
                      
                                                    
            
                      
                                                                                    
                                                      
                                        
                                                
                                                        
                                                    
                 
                 
                         
                   
                                                     
                                                        
                                                      
                                              
                                           
                                                                      
                                     
                   
                                                  
                                                  
                                    
                                                                  
                                                      
                                                                          
                                     
                                             
          
                                                              
                                               
                             
        
                                                      
                                                      

end

end AVenhance.Infra.Flow
