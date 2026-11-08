/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsApprox
public import RegularityStructures.BPHZ.ChaosLimitMomentsCylinder

/-!
# Riemann-type approximations of tested polynomial fields

For a random field `ψ`, kernel `k`, test function `g` and polynomials `P₁, P₂, P₃` put
`X(ω) = ∫ (∫ k(y, w) P₁(ψ(ω, w)) dw · P₂(ψ(ω, y)) + P₃(ψ(ω, y))) g(y) dy`.
Replacing `ψ(ω, ·)` by `ψ(ω, π ·)` for a finitely-valued measurable sampling map `π` gives
`chaosIntegral`, which is a polynomial of total degree at most
`max (deg P₁ + deg P₂) (deg P₃)` in the finitely many values `ψ(ω, b)`, `b ∈ range π`, with
deterministic coefficients (`exists_mvPolynomial_chaosIntegral`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*}

                                                      
                                                                                         
                                                              
                                 

                                                                               
                                                                          
                                                                                     
                          
                                                                             

                                                                                 
                                                                         
                                                                                            
                                          

end RegularityStructures

end

public section

open MeasureTheory MvPolynomial

namespace RegularityStructures

variable {Ω : Type*}

                                                                                
                                                                 
                                                               
                                                                         
                                                                               
                                                                          
                         
                           
                                                                      
                                                                               
                                                                                 
                                              
                                                                                               
                                                
                                                                         
                                                                       
                         
                                                                                                 
                   
                                                               
                                                                                    
                                              
                     
                                                                                 
                                                                                    
                                                                                  
                                                         
                                                                          
                                       
             
                         
                                                        
           
                                                   
          
                                                   
                                 
                                                                     
                                                              
           
                        
                 
                                 
                                                                                        
                                                                                  
                                                                
                                                                
                                                                             
                                                                      
           
                                             
                           
                                                                          
                                                                              
                                              
                                                                                         
                                                         
                                                   
                                                   
                                           
                                  
                                                                                     
                                         
                                                   
                                           
                                  
                                          
           
                                                                   
                                       
                                  
                                               
                         
                                               
          
                                               
          

end RegularityStructures

end
