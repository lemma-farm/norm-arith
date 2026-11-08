module

public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.KilledAffineLoad

@[expose] public section

/-!
# Positivity of the affine boundary response

The average gradient is fixed throughout the affine boundary class. This
gives finite-cutoff strict positivity directly from ellipticity, without a
boundary trace theorem. It does not provide the uniform inverse moments of
Lemma 12; those still require the coarse estimates of M.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

                                                                                           
                                      
                                                               
                                                          
                                                                              
                                                                                   
                       
                                                              
                                           
                                                            
                            
           
      
                                                                 
                             
                                                                      
                                                        
             
                                                                                     
                  

                                                                                              
                                   
                                                               
                                                             
                                                
                                                                                
                                                              
                                               
                                                                                       
                             
          
                                                                               
                                  
                                        
                                                                                           
                                                    
                                                
                                                                                 
                                                              
                         
                                            
                                       
                    
                     
                                                            
                                                 
                               

end SubdiffusiveProcess
