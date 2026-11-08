module

public import SubdiffusiveProcess.Sobolev.GradientRange
public import Mathlib
@[expose] public section

/-!
# Mean-zero Sobolev data and the affine Neumann load

The domain has finite Lebesgue volume. Mean zero means its actual volume
integral vanishes. The affine Neumann load is the sum of the coordinate
volume integrals of the weak gradient; identifying its boundary-flux formula
is a separate trace/divergence theorem.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

                                                                           
                                            
                                                                                       
                

                                                               
                                        
                                                                
                                                                                        

                                                                  
                                                         
                                    
                                                            
                   
                         
                                                              
                                                            

                                                                              
                                                           
                                                                          
                                  
                                                                                         

                                                                           
                                                          
                                                         
                                                                
                                                                        
                                                                            
                                             

                                                                               
                                       
                                                              
                                              
                                                                                  

                                                            
                                                                    
                                                                          

                                                                      
                                                                         
                                        
                                                                
                                          
                                                                                                 

end SubdiffusiveProcess
