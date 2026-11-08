module

public import SubdiffusiveProcess.Sobolev.KilledGraph
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section

/-!
# Closed gradient ranges and volume loads

Only the finite tuple of scalar L2 spaces receives a Hilbert norm. Spatial
coordinates retain their ordinary product norm; no vector-valued Lp coercion
through a Euclidean-space wrapper occurs. The Poincare estimate below is an
explicit foundational input on a concrete closed subspace of the weak graph.
It is not a model convergence or regularity assumption.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

                                                                                        
                                                            
                                      

                                                                             
                                                              
                                                                                                
                                   

                                                                                  
                                                     
                                                         
                           

                                                                                
                                                                                     
                                 

                                                                 
                                                                  
                                            
                                                     
                    
              
                                                                                  
                      
                                                  
                                                          
             
                                                    
                                                            
                                           

                                                                                         
                                                                                  
                                                                          
                                                       
                                                                                                              

                                                                                          
                                                                         
                                                       
                                                                          
                                                   
                                                 
                                                      
                                                                                                     

                                                                                  
                                                          
                                                       
                                                                          
                                                                  
                                                  
                                                       
                                      
                                                                                                 

                                                                               
                                                                  
                                                       
                                                                                  
                                                                                        

                                                          
                                                                 
                                                    

                                                                                                 
                                                                      
                                                                                      
                          
                   
                                                        

                                                                  
                                                        
                                                       
                                                                        
                                                                                  
                                                                                                          

                                                                        
                                                                     
                                                       
                                                                        
                              
                                                                       
                                                                                  
                                                                   
                                               
                                                                      

end SubdiffusiveProcess
