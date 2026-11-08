/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Wegner.Gershgorin
public import FroehlichSpencer.Infra.Wegner.Averaging
public import Mathlib
/-!
# Resonance events: measurability, locality, and the combined Wegner/Gershgorin bound

For `H(v) = A + diagonal (v|_Λ)`, the resonance event
`{v | ∃ i, |λ_i(v) - E| ≤ κ}` is measurable, depends only on the coordinates in `Λ`, and has
`productMeasure μ`-probability at most the minimum of the Wegner bound
`ρ · 2κ · |Λ|` and the Gershgorin bound `|Λ| μ {t | |t - E| ≤ K + κ}`
(Fröhlich–Spencer (1983), Appendix C, Fröhlich–Spencer (1983)).
-/

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ENNReal

namespace FroehlichSpencer.Infra

variable {ι : Type*} [DecidableEq ι] {Λ : Finset ι} {A : Matrix Λ Λ ℂ}

                                                                                    
                              
                                                                                        
                                                                                             
                                   
                                                                                                 
               
           
                                     
                                                                                 
                                                               
                                                       

                                                                                
                                      
                                                                                        
                                                                                                  
                     
                                                                             
                                                                                              
                                                                                
                 
             
                 
                 

                                                                                        
                                                                                        
                                                                                         
                            
                                 
                                                                                      
                                                                                     
                                                                            
                                                                          

end FroehlichSpencer.Infra
