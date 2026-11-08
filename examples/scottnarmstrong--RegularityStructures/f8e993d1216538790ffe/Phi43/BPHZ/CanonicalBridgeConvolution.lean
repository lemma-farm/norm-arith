/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeKernel
public import Phi43.BPHZ.CanonicalBridgePeriodise
public import Phi43.BPHZ.PsiGaussianVectorContinuous
public import Phi43.BPHZ.TreeI3PsiField

/-!
# Periodisation of the Hairer convolution

Let `proj y = (y.1, torusProj y.2)` be the projection `ℝ × ℝ³ → ℝ × T³`.  For a continuous
`g : ℝ × T³ → ℝ` with periodic lift `g ∘ proj`, convolution with the Euclidean kernel
`hairerKernel N` on `ℝ⁴` agrees with convolution with the periodised kernel `hairerKernelTorus N`
on `ℝ × T³`:
`∫_{ℝ⁴} K(y - w) g(proj w) dw = ∫_{ℝ × T³} K^♯(proj y - u) g(u) du`.
Hence `hairerConvolution N (ξ ∘ proj) y = hairerPsiField N ξ ω (proj y)`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

                                                                    
                                                                          

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

                                                              
                                            

                          
                                                  
                                                                   
                        
          
                                 

                                                                                                 
                                                                     
                                                                                          
                  
                                                                                 
                                                                
                                                                     
                                                                                                 
           
                          
            
                                                          
                                             
                                            
                 
                     
         
                                               
                                                              
                                              
                                          
            
                         
                                                                                  
               
        
                                                           
                          
                 
                                                                                  
         
                                            
                                                                           
           
                               
         
                        
          
                                                                                                       
      

                                                                
                                                                       
                                                                                      
                          
                                                          
                                                                
                                                           
                                                                          
                                                                                   
                          
                                                                                             
                                                                           
                                                     
                                  
                             
                                              
                                                                                  
                                 
                                                                    
                                 

end RegularityStructures.Phi43

end
