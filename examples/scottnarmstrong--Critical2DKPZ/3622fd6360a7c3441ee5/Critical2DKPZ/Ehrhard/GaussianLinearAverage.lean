/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.GaussianSmoothClass
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Joint regularity of Gaussian linear averages

Allowing the parameter to contain both the center and the scale gives joint
space-time regularity after composition with the OU coefficient curves.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open Critical2DKPZ.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace Critical2DKPZ.Ehrhard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                                                               
                                                                       
                                                                 
                                                                   
                                          
                                                               
              
                                                                    
                                                                             
                                                               
                                          
                             
                        
                                        
                                              
                                                  
                                                  
                                                                                  
                                                                
                                                                                                  
                                                                                 
                                                                                           
                                                                  
                                       
                                    
                                                                  
                                                      
                               
                                                                        
                  
                                       
                                                                                  
                                           
                                               
                                                                 
           
        
                                              
                                                                  
                                       
              
                                                           
                                                            
                                                                         
                                       
                                                                         
           
                                                                           
                                                                      
                                             
                   
                
                                                                     
          
                                                       
                                                                  
                                                                    
                                                              
        
                                               
                                                 
                                                          
                                                                  
                                                                           
                                                                       
                                                      
                                                                                                 
                                                               
                                                                             
                                        
                                                                   
                                                                                                         
                                                             
                                             
                                                                  
                                       
                                                                               
                                      

                                                                                               
                                                                        
                                                                 
                                                                   
                                          
                                                                 
                                                                           
                                   
                                                     
                                                                         
                                                                                 

end Critical2DKPZ.Ehrhard

end
