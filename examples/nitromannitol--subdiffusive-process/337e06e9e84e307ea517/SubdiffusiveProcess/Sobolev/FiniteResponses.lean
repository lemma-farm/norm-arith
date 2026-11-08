module

public import SubdiffusiveProcess.Sobolev.WeightedGradient
public import SubdiffusiveProcess.Sobolev.MeanZero

@[expose] public section

/-!
# Finite-cutoff killed and Neumann weak solutions

The variation spaces and loads here are concrete. The only analytic input
left explicit in these declarations is the ordinary Poincare inequality on
the chosen domain (or its mean-zero version). Coefficients are genuine L∞
functions with a positive lower bound. No limit operator or model regularity
estimate is assumed.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

                                                                
                                                     
                                                               
                                                      
                                                                   
                        
                                                                          
                      
                                                            
                                                                  
                                               
                                                                                    
                                                                          
                                            
                                                                
                                                                                         
                                    

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

                                                                        
                                                                         
                                                                   
                                                       
                                                                 
                                                        
                                                                   
                        
                                                                          
                      
                                                                
                                                                  
                                               
                                                                                    
                                                                            
                                              
                                                                  
                                                                                         
                                    

                                                                                  
                                                     
                                                                 
                                                        
                                                                   
                        
                                                                          
                     
                                                                
                                                                  
                                                            
                                                                                        
                                                                            
                                              
                                                                            
                                                        
                                        
                                                                                         
                                                     

end SubdiffusiveProcess
