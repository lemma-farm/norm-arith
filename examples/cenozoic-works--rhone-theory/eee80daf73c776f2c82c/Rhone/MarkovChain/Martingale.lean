/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Hitting
public import Mathlib
public import Mathlib.Probability.Process.HittingTime

/-! # Martingales from harmonic functions and optional stopping -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {h : S → ℝ}

                                                             
                                                                                     
                         
                                                                                           
                    
                                                 
                                                                           
                                             

                                                                           
                                     
                                                                             
                                                                                     
           
                                                                  
                                                                    
                                          
                                                                                             
                                                                                     
              
                                             
                                                  
                 

                                                                        
                                                                                             
             
                                                                                     
                                     
                                         
                                             
                                                 
                                                   
                                                                              
                                                                          
                            
                                
          

                                                                      
                                                                                             
                                         
                                                                                 
                                                                  
                                       
                                                                                    
                                                               
                                                                                         
                                
                                                                                  
                                                                   
                                   
                                                    
                                                                     
                                                                   
                                                                               
                                                                                        
                                                                                  
                                                                                       
                      
                                                    

                                                                                      
                                                                         
                                                    
                                                                                        
                                         
                                             
                                                                                          
                                                              
                                                                                

end Rhone.MarkovChain.FinChain
