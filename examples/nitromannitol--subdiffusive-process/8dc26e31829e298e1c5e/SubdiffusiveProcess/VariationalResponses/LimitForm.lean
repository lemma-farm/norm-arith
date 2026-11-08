module

public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.Sobolev.ResponseRecovery
public import Mathlib
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- `E(u)` of `eq:mfd-18`:
the dual energy of the killed inverse `G`. -/
def limitFormEnergy (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) : EReal :=
  ⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)

                                             
                                                                           
                                                      

                                                                
                                                                                     
                                                                       

                                                                
                                                                            
                         
                                                                        
                                                     
                                    
                                                              

                                                                                   
                                        
                                          

                                                       
                                       
                                                                       
                           
                                                         
                                     
                                                                  
                                                  
                                
                                                 
                                                                              
                                      
                                               
                                                                                     
                                           
                          
                                                                              
                             
                                                                                       
                                                
                                     
                                                                
                                           
             
                    
                                                                             
              
                                                                           

end SubdiffusiveProcess
