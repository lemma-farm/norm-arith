module

public import SubdiffusiveProcess.Sobolev.ResponseSpace
                                                                 
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# Canonical inverse responses: coefficient order and potential comparison

Coefficient order is reversed for inverse responses. Scalar homogeneity and
the attained variational formula prove the exact exponential comparison used
by the finite-band compactness argument. These are actual responses on the
concrete Sobolev spaces; no comparison property is assumed of the response.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

                                                                
                                                                               
                               
                        
                                  
                                   
                                                         
         
                                          

                                                                         
                                                                                         
                                                           
                                                                 
                                                                
                               
                                                  
                                                  

                                                                      
                                                            
                                                                      
                                                                                         
                                                                                                       
                                                                  
                                                                     
                                                                                

                                                                                    
                                                                             
                                                                                     
                                                                     
                                                                  
                                                     
                                                                       

                                                                 
                                                                                    
                                                                                     
                                                                               
                                 
                                                                        
                                                                  
                                
                              
        
      
                                                                
                                                                                           
                                                                              

                                                                           
                                                                
                                                                            
                                                                                               
      
                           
         
                                     
                                                                      
                                                   

                                                                                  
                                                               
                                                                            
                                                                                             
                                                                            
                            
     

                                                                                 
                                                       
                                                            
                                                               
                                                                 
                                        
                                                                 
                                       
                                                                   
                                                                      
                                                                                                      
       
                                                                                                      
                 
                                         
                                                                      
       
                                                                                               
                    
                 
                                                                     
                                                

end SubdiffusiveProcess
