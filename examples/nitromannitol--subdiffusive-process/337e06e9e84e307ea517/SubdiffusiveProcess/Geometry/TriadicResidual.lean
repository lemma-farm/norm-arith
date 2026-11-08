module

public import SubdiffusiveProcess.Geometry.OddGridResidual
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Vanishing geometric remainder on the actual triadic grid

The odd grid with middle index `3^J / 2` has exactly `3^J` intervals per
coordinate. Its actual unresolved volume fraction is at most `d / 3^J`
and tends to zero. This limit is geometric and deterministic; it is taken
before any cutoff-uniform moment estimate in the reflection argument.
-/

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The middle label in a coordinate subdivision of depth `J`. -/
def triadicHalf (J : ℕ) : ℕ := 3 ^ J / 2

                                                                           
                                                                                 
                                                               
                              
                                        
                    
       

                                                                         
                                                                                     
                                              

                                                                                            
                                                              
                                                                                  
                                                           
                                                                            
                                                                      
                                        
                                        
                                                                  

                                                                        
                                                         
                                                                                  
                                                           
                                                                            
                                                                      
                                   
                                                                     
                                                    
                                                               

                                                                      
                                                                   
                                                                          
                         
                                                             
                                                                              
                                                                                         
                                                                                                 
                                                    
                                                  
                                                                                      
                                                                 

end SubdiffusiveProcess
