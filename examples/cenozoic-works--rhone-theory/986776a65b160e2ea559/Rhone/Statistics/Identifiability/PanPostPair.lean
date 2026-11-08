/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.LawSeparation
public import Mathlib
/-! # Surviving pair under arbitrary time-varying panmictic rates -/

@[expose] public section

open scoped Matrix
open Set Finset
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

                                                                                     

                    
                                                                                         
                                                    
                          
                                                                           
                                                                                         

                                
                                                                          
                                                     
                                                               
                                                                                               
                                                              
                                                                             
        

noncomputable def panPostGenerator (rate recomb : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-rate-recomb,recomb], ![2*rate,-3*rate]]

                                                       
                                                         
                                                            
      

                                                                                  
                                          
                                                                  
                                                                     
                                                               
                    
                      
                                               
                     
                            
           
      

                                                              
                                                                               
                                                                                              
                                                                                    
                                                            
                                                                              
                          
                                                                              
                          
                                                                   

                                                        
                                                                     
                                                      
                                                                      
                                          
                                                                             
              
                                                
        
                                                        
                                                  
                                                
         

                                                                                  
                                                       
                                                                
                                                                      
                                                         
                                               
                                                                          

end Rhone.Statistics.Identifiability
