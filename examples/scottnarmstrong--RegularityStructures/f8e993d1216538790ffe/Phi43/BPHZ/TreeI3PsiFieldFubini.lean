/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.RandomFieldFubini
public import RegularityStructures.Torus.Basic

/-!
# Fubini for the product of two tested random fields

For integrable kernels `g, ḡ`, jointly measurable fields `Y, Ȳ` and random variables `a, b`,
if `Y(w) a Ȳ(w̄) b` is integrable with `E|Y(w) a Ȳ(w̄) b| ≤ M` uniformly, then
`E[(∫ g Y) a ((∫ ḡ Ȳ) b)] = ∫∫ g(w) ḡ(w̄) E[Y(w) a Ȳ(w̄) b] dw dw̄`.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
  {Y Y' : Ω → SpaceTime → ℝ} {a b : Ω → ℝ} {g g' : SpaceTime → ℝ}

                                                                               
                                       
                                                        
                                                          
                                                                                     
                                      
                                                                       
                                                                                        
                                                                           
                                                            
                                         
                                                                                   
                                          
                                                                                           
                                                                                          
                                                                                              
                                                                        
                                 

                                                     
                              
                                                        
                                                          
                                                                                     
                                      
                                                                       
                                                                                        
                                                                     
                                                   
                                                      
                                                                      
                                                                           
                                                                                              
           
                                                                                 
                                                     
                                                                                                  
                                                                                
                           
                               
                                                                                       
                                                                                       
                                                     
        
                                                                      
                                          
                                                                      
                                                           
                                         
                                                                     
                                 
               
                                                                          
                 
                               

                                                                                             
                                         
                                                        
                                                          
                                                                                     
                                      
                                                                       
                                                                                        
                                                                 
                                                                          
                                                                             
                                                                              
                                                                                 
                         

end RegularityStructures

end
