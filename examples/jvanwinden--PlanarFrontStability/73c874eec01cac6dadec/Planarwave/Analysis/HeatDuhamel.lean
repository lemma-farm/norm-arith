/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.DelayedHeatForcingSmoothing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Continuous heat Duhamel trajectories

These facts support both the tracking cancellation and the construction of
the forced Cole--Hopf mild solution. All integrals are BUC-valued; continuity
of the heat operators in operator norm at time zero is not assumed.
-/

open MeasureTheory Set

namespace Planarwave

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The transverse heat Duhamel integral in real BUC space. -/
def heatDuhamel (a : ℝ) (g : ℝ → BUC E F) (t : ℝ) : BUC E F :=
  ∫ r in (0 : ℝ)..t, heatFlowBUC a (t - r) (g r)

       
                                                                                
                    

                                                                                        
                                                                     
                                       
                                                                         

                                                                       
                              
                                                                              
                                   
                                                                       
                                                         

                                                   
                                                     
                                                                                     
                                          
                                     
                                                       
                                                                     
                                                       
                                                                     

                                                              
                                                                   
                                                                           

                                                                              
                                                                          
                                                                          
                                       
            
                          
            
           

                                                                          
                                                                      
                                                                       
                                                                        
              
                            
                                                                  
                                                             
                                                        

                                                                        
                                                                      
                                                                               
                                                       
                                                                   
                                                    
                                                                           
                                                      
                                                          
                                                                                              
                                                                                              
                                                                                   
                                                       
                                                      
                                                                            
                                                               
                                                          
                                                                                        
                                                                  
                                         
              
                            
                                                                  
                                                                              
           
        
                 
                                                                       

end

end Planarwave
