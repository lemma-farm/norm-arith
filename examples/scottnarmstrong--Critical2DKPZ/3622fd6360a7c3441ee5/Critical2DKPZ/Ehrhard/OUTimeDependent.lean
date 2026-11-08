/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.OUBackwardDerivative

/-!
# The time-dependent OU interpolation derivative

The outer backward-time generator cancels the spatial generator of the inner
observable. Bounds here are ordinary space-time regularity bounds; all
Gaussian integrability and generator identities are proved.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology

namespace Critical2DKPZ.Ehrhard

                                                                                  
                                                                
                                                                                
                                                         
                                            
                                                                
                                     
                                                                              
              
         
                                                                    

                                                                                       
                                                              
                                                                
                                                                
                                            
                                                      
               

                                                                             
                                                 
                                                                                   
                                                
                                                                 
                                                                                      
                                
                                       
                                                           
                     
                                         
                                                     
                                                             
                           
                                 
                            
                                                             
                                              
                                                              
                                                 
                                       
                                                 
                                                                            
                                                             
                                                                          
                               
                                                                    
                                                              
                                                             
                                                                
        
                                                                   
                                       
                                                                                                            
                              
                                                                    
                                                                                           
                                                                 
                                                                  
                                                             
                                                                            
                                       
                                                                      
                                 
                                                                         
                
                                                                
                                                                            
                                                   
                                                                                   
                                                                      
                                        
                               
                                                                 
                   
                        
                                                                          
                                                                                 
                                                                               
                                                             
                                             
                                                                
                                                                  
                                                     
                                    
                  
                                                           
         
                                           

end Critical2DKPZ.Ehrhard

end
