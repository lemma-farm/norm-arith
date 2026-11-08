/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Location
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Wegner.Gaussian
public import FroehlichSpencer.Infra.ProductMeasure
public import Mathlib
/-!
# Gershgorin resonance: an eigenvalue near `E` forces a site potential near `E`

Fröhlich–Spencer (1983), Appendix C, (C.5) (Fröhlich–Spencer (1983)), generic form:
if `A` is Hermitian with row sums `∑ y, ‖A x y‖ ≤ K` and `A + diagonal v` has an eigenvalue
within `κ` of `E`, then some site has `|v x - E| ≤ K + κ`.

Consequently, under
`productMeasure μ` the probability of such an eigenvalue is at most
`|Λ| μ {t | |t - E| ≤ K + κ}`, with an explicit bound for the Gaussian law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped ENNReal NNReal

namespace FroehlichSpencer.Infra

                                                                                           
                                                                                            
                                                                                      
                                
                                                                  
                                     
                
                                                          
                                       
                                          
                                 
                                                           
                                                                     
                   
                         
                         
             
                                                   

section

variable {ι : Type*} [DecidableEq ι] {Λ : Finset ι} {A : Matrix Λ Λ ℂ}

                                                                                             
                                                                                     
                                 
                                                                                      
                                            
                                                         
                                                   
                                    
                                                                                    
                                                                                   
                              
                        
                                                                           
                               
                                        
                                                                              
                                     
                                              
                                                                              
                                                           

                                                                                         
                                                                                               
                                                  
                                                                                      
                                                                 
                                                        
                                                                                        
        
                                                                                   
         
                                                              
                                                                   
           
                                  

end

end FroehlichSpencer.Infra
