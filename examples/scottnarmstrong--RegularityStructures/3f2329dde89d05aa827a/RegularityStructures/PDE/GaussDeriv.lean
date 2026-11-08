/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatOp
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivative and first moment of the unit Gaussian on `ℝ³`

For `γ₁ = gaussKernel 1`:

* `integrable_norm_mul_gaussKernel_one`: `z ↦ |z| γ₁(z)` is integrable;
* `fderiv_gaussKernel_one_single`: `∂_i γ₁(z) = -(z_i / 2) γ₁(z)`.

These are the inputs of the integration by parts behind `∂_t P_t g = P_t Δg`.
-/

public section

open MeasureTheory Real Filter

namespace RegularityStructures.PDE

                                           
                                                        
                                                                 
                                              
                                     
                                                               
                                       
           
                      
                                                    
                                                          
                                                                 
                                                     
                                                                                      
                                                         
                                                   
                                                                                        
                          
      

                                         
                                             
                                                               
                                                                             
                                                                          
                                                                                         
                                      
                                     
                                                                            
                                         
                                                                                                 
                       
                                                                                
                       

                                                                     
                                                                           
                
                                                                     

                                                                               
                            
          

                                      
                                                                   
                                                                                   
                                                                            
                             
                                                                                            
                                            
                                                                            
                                       
                                                                             
                                                                                             
            
                                             
                                                                   
                                                                                                
                                                                                    
                                
                                                                 
                                                                                     
                          
                
            
            
            
                                                             
                        
                    
                                                                                           
               
        
                   
                    

end RegularityStructures.PDE

end
