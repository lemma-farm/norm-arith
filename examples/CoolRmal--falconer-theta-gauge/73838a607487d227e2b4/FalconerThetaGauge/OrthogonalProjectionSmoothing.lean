module

public import FalconerThetaGauge.OrthogonalProjectionDensity
public import FalconerThetaGauge.FourierReconstructionPairing
public import Mathlib
/-!
# Concrete low-pass approximants of the orthogonal densities

The inverse square-integrable Fourier approximant is identified with the actual
Schwartz kernel convolved against the source measure. Its pointwise bound is
therefore a consequence of probability mass, as required in Lemma 5.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter SchwartzMap FourierTransform
open scoped ENNReal ContDiff

namespace FalconerThetaGauge

                                                                
                                                      

                                                                                 
                                                    
                                                                                               
                                                                                                     
                                       
                                                                     
                                            
                                                                        

                                                                           
                                  
                                                                    

                                                                         
                                  
                                    

                                                                                         
                                   
                                              
                                                                           
                                                             
                                                                             
                                                                                    
                     
                                                   
                                
          
                         
                                                                         
                                                                                 
                              
      

                                                                                   
                                                                                                   
                                          
                                                                              
                                                                                     
               
                                                                          
                                                                
                                                                                     
                                                                                
                                                

                                                                                               
               

                                                                                                
                                           
            

                                                                                       
                     
                                                            
                                                            
                                                           
                                                                                   
                                                                            
                                                               
                                                                               
                                    
                                                
                                                                                                
                                 
                                                                                     
                                                            
                                                                 
        
                                            

end FalconerThetaGauge
