module

public import SubdiffusiveProcess.Sobolev.ResponsePerturbation
public import SubdiffusiveProcess.Sobolev.PotentialCoefficient

@[expose] public section

/-! # Local potential changes on the actual Sobolev responses

The coefficient assumptions for relative perturbation are derived from the
actual exponential identity. The constants depend on the changed potential
only, and the support and original local energy are retained.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

                                                                                           
                                                   
                                                                     
                                    
                                                                                       
                                                           
                                                                                                     
                                                                                     
                                                                  
                                                                                                  
                                                                                                 
                                                                                         
                                                                                         
                                                                                                              
                                                            
                                                                                     
                         
           
                                                                                   
        
                                                                        
                                                      
                                                                                 
           
                                                                                   
            
                                             

                                                                                      
                                                                  
                                                                     
                                                           
                                                                                     
                           
                                      
                                            
                                   
                                   
                                                                  
                               
                            
                                                      
                                                             
                                                    
                                                                                 
                                                                  
                                                                                          
                                                           
                                                                   

                                                                                       
                                                                    
                                                                     
                                                           
                                                                                     
                              
                                      
                                            
                                     
                                     
                                                             
                               
                            
                                                                              
                                                        
                                                    
                                                                                     
                                                                  
                                                                                            
                                                           
                                                                   

end SubdiffusiveProcess
