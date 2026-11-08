/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.GaussianHeat
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiating a time-dependent Gaussian affine average

A local polynomial bound for a smooth space-time test function gives an
explicit Gaussian integrable majorant for its path derivative. This is the
integral differentiation step for the nonlinear OU interpolation.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open Critical2DKPZ.Gaussian (standardGaussianMeasure)
open scoped Topology

namespace Critical2DKPZ.Ehrhard

                                                                   
                                                   
                                     
      
                                                  
                         
                                      
                                                                         
                                

                                                                           
                                                   
                                               
                                     
                                  

                                                                                                                                                      
                                                                             
                                                  
                                       
                                           
                                         
                                         
                                               
                                                                       
                                       
                                                             
                                                                              
                                                              
                                           
                
                                              
                                                                            
                                                                                         
                                                  
                                                                            
                                   
                                                   
                                                        
                                                
                                                                       
                                             
                                                      
                                                   
                                            
                                                                 
                                                          
                                       
                                                                   
                                                                 
           
        
                                                               
                                                                      
                                                                  
                                                            
                                                                  
                              
                                                                    
                                                   
                                                                                       
                                       
                                                         
                                                                           
           
                                                                      
                                         
                                                       
                                                            
                                                   
                   
                
                                                                
                                             
                 
                      
                                          
                                                                                 
                                                                                          
                                                                               
          
                                                                          
                                                                      
                                                                    
                                                              
        
                                                            
                                                                           
                                                   
                                                          
                                                        
                                                                                   
                                                        
                                                
                                                                    
                   
                
                                                                                    
                                                                                                    
                                                                                     
                                                                          
                                                                            

                                                                            
                                                            
                                                                         
                                                                  
                                       
                                     
                                                       
                                
                                       
                                                             
                                                                              
                                                                        
                                           
                                                      
                                             
                    
                                                           
                               
                                                          
                                                             
                                                                                           
                                                                                       
                                                     
                                              
                                                                      
                                                     
                                                  
                                                                     
                              
                                                 
                                                                               
                                      
                                                                                     
                                      
                                                                                     
                                                                             
                                                                          
                                                            
                             
                                                  
                                   
                                                                                              
                                                                                              
                
              
                               

end Critical2DKPZ.Ehrhard

end
