/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorMoment
public import RegularityStructures.Analysis.Semigroup.Pairing.Fubini
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Algebra

/-!
# The generator identity for the auxiliary semigroup

For `φ : ℝ⁴ → ℝ` smooth with compact support,
`Q_h φ(z) - φ(z) = ∫_0^h Q_v (L φ)(z) dv`, with
`L = (4π²)⁻¹ ∂₀² - (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴` (`parabolicGenerator`), i.e.
`parabolicSemigroup.IsGeneratorPair φ (parabolicGenerator φ)`.

Route: `F(v) = Q_v φ(z)` is differentiable on `(0, ∞)` with
`F'(v) = ∫ (∂_v q_v)(z - y) φ(y) dy` (`hasDerivAt_apply_parabolicSemigroup`), which equals
`Q_v(Lφ)(z)` by the pointwise heat equation and integration by parts
(`integral_parabolicTimeDeriv_mul`); `F(v) → φ(z)` as `v ↓ 0` (`abs_apply_sub_le`); and `F'` is
bounded and measurable (`abs_apply_le`, joint measurability), so the fundamental theorem of
calculus applies on `[0, h]`.
-/

public section

open MeasureTheory Filter Topology Real Set
open scoped ContDiff

namespace RegularityStructures

                                                                                           
                                                                               
                                                            
                                                                                  
                                 
                                                                      
                                               
                                                                          
                                                
            
                                                     
                                           
        
        
                                                                                              
                                                                      
                                                                           
                                                                       

                                                                    
                                    
                                                                                         
                                                                                                  
              
                                          
                                              
                                                                                                       
                                          
                                                   
                                                                                         
                                                                                  
                     
                                                                                  
              
                                                                        
                                                         
                                      
                                              
                    
                                      
                                             
              
                                             
              
                                                                            
                  
                                                 
                   
                    
                          
                          
                                                                           
                                                                                
                                                 
                                                                 
                                                                         
                                                                             
                                                                         
                                             
                                             
                                     
                                                           
                                                                                           
                                                            
                                                                          
                                                                                                               
                                               
                                                                                       
                                   
                                                                                              
                         
                                                             
                                                                          
                                    
                            

end RegularityStructures

end
