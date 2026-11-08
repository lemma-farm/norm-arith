/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Zeta23.Defs

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/

                                                                                              

                                                                                              
                                                                                  
                                                                                         
                                                                   

                                                                                   
                        

                                                                                     
                        

                                                 
                                                                       
                                                       
                                          
                                             
                
                
                                  
         
         
           
            

                                                               
                                                
                                          
                                                    
                     
           
            

                    

                                                                                                   
                                                                                         
                                                                           

                                                                                           
                       
         
                                       

                                                             
                                                    
                                       
                                               
                                   
                               

                                                                                       
                                                                
                                              
                                                            
                                        
                                                                                              
               
                       
             
                 
          
                                         

                                                                         
                                                                                               
                                                      
                                                               
                                                                                                       
                                                                                                  
           
                                                                  
                                                       
                                  
                                                                      
                                                                               
                                                                    
                                                        
                                                 
                                        
                                                                              
                                                                         
                                                                             
                                                                                                            
                  
                                      
                                                              
                                            
                         

                                                                                                         
                                                                                           
                                                                      
                                               
                                                                                 
         
           
      

                                                                                        
                                                                
                                                                                            
            
                              

                                                                                      
                                                                 
                                                                   

                                                              
                                           
                                                                        
                                              
                                                                                    
                                                                                 
                                                         
                                                          
              
                            
                                                                                
                               
                                             
                                                                                       
                                       
                                                                                 
            

                                                                                            
                                                                     
                                                           
                                                                                      
                                  
                                         

end Zeta23
