module

public import SubdiffusiveProcess.Sobolev.AffineData

@[expose] public section

/-!
# Affine loads vanish on killed variations

For a compactly supported smooth function, each coordinate derivative has
zero volume integral. Continuity passes this identity to the concrete H1_0
completion. Thus affine boundary perturbations have the prescribed average
gradient, with no boundary-flux identity imported as an assumption.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

                                                                                  
                                      
                                                               
                               
                                                                            
                                                                     
                                      
                                                        
                                                    
                                
                                                                
                                           
                                                         
                                                         
                                                                        
                           
                                                                                
                                                                                         
                        
                                                                                         
                                             
                                                                 
                                               

                                                                              
                                        
                                                               
                                                
                                                                             
                                                                             
                                                                    
                                              
                       
                                                                            
                                  
                                                                   
                                      
                                                                       
                                        
                                                     
                     

end SubdiffusiveProcess
