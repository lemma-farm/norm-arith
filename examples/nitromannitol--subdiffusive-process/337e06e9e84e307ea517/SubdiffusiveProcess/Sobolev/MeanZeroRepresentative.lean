module

public import SubdiffusiveProcess.Sobolev.AffineData

@[expose] public section

/-!
# The mean-zero representative of a Sobolev function

Subtracting the actual volume mean identifies a local H1 function with an
admissible competitor in the mean-zero Neumann space, preserving its weak
gradient. This is used to test the inverse response with the Dirichlet
minimizer in the nonnegativity proof for the diagonal response defect.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

                                                                                          
                                 
                                                               
                                                             
                                                           
                                                                 
                                                
                                                 
                                   
                                                                                      
                                                                                     
      
                                                                    
                             
                                                                                    
                    
                                                                                  
                                        
               
                                                                                                          
                                                                        
                                                                   
                                                      
                                                                 
                                                             
                
          

                                                                                      
                                           
                                                               
                                                             
                              
                                                           
                                                                     
                                                              
                                                            
                                                                 
                                                
                                                                                
                
                                                      
                                                                              
                                    

                                                                 
                                              
                                                               
                                                             
                              
                                                                                         
                                 
                                                                                
          
                                                            
                                                 
                
                                                      
                                                                                              
                     
                  
       
                   

end SubdiffusiveProcess
