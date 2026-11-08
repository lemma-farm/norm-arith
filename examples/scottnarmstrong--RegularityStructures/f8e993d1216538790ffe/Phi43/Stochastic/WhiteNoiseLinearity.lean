/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.AnnealedNoiseTorus

/-!
# Almost-sure linearity of a Gaussian white-noise family

The definition of `IsWhiteNoise` specifies the joint centred Gaussian law and covariance of every
finite family of pairings.  Those finite-dimensional laws force the family to be linear almost
everywhere: the variance of `W (h + g) - W h - W g` and of `W (a • h) - a * W h` is zero.  These
identities are the probabilistic bridge needed when a spatial heat convolution is rewritten as a
single white-noise pairing.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

                                                        
                                                                
                                                   
                                          
                                                                            
                                
                                             

                                                                            
                                                                   
                                 
                                                    
                                          
                                                 
           
                               
                                                                             
        
               
                                                       
                                                                       
                                               
                                           
                                                                                 
                                           
                         
                          

                                                     
                                                             
                                                
                                          
                                        
           
               
                      
                    
                     
                                                             
                                                   
                             
             
                 
                        
                      
                                    
                                                                     
        
                                     
                                                           
                               
                                
                                    
            
                  
                                                                          
                                                                                
                                    
            
                                                                            
                                                                        
            
                                
        
                                  
                                              
                       
            
                                                  
        
                                                                    
        
                                                         
                               
                                
                                                      
            
                       
                                         
                                                                          
                               
                                          

end RegularityStructures

end
