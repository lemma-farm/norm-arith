/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/Real/SpectralBridge.lean`.
* Extraction class: **moved**, not restated.  The five theorems are the **real-scalar
  counterparts** of `SpectralOrder/Complex.lean`, name for name, and they were sitting in the
  paper library while depending on nothing from it: their only `DavisKahan` import was the
  alias layer `BoundedOperator/Compat.lean`, whose two names used here -- `Reduces` and
  `opNorm_starProjection_sub_le_of_formBounds` -- resolve into `ForTauCeti` already.
* Namespace: `TauCeti.DavisKahan.Experimental.Foundation.RealSpectralBridge` became
  `TauCeti.SpectralOrder.Real`, matching its complex twin rather than carrying a paper's name
  and a staging word into the library staged for Tau Ceti.
* Original authors / copyright: Jon Crall; Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** -- imports are `ForTauCeti` leaves and Mathlib.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import Mathlib

/-!
# The real spectral-order bridge

From the **spectrum** of a symmetric real operator to **quadratic-form bounds**,
and from there to the real Davis--Kahan estimate on restrictions.  This is the
real-scalar counterpart of `SpectralOrder/Complex.lean`, name for name.

## Main results

* `upperFormBoundOn_top_of_spectrum_subset_Iic` — `spectrum ℝ A ⊆ Iic c` implies
  `A.UpperFormBoundOn ⊤ c`.  This is the bridge; everything below is transport.
* `lowerFormBoundOn_top_of_spectrum_subset_Ici` — its negation.
* `upperFormBoundOn_of_restriction_spectrum_subset_Iic` and
  `lowerFormBoundOn_of_restriction_spectrum_subset_Ici` — the same on a reducing
  subspace.
* `opNorm_starProjection_sub_le_of_restriction_spectra` — the sharp real
  Davis--Kahan bound `‖P_U − P_W‖ ≤ ‖B − A‖ / g` from the spectra of the actual
  restrictions.

## How the bridge is proved, and why not the other way

**Over `ℝ` there is no continuous functional calculus to appeal to**, so the
obvious route — rewrite the complex CFC theorems under real scalars — is not
available: the missing instance *is* the problem.  Two routes were open, a
norm-preserving complexification and constructing the real CFC instance
outright; the proof below takes neither, and instead runs the direct
Rayleigh shift, which needs no new instance at all.

Choose `m > ‖A‖` and set `S = A + m • 1`.  Translating the spectrum
(`spectrum.singleton_add_eq`) puts every spectral value of `S` in `(0, m + c]`;
`ContinuousLinearMap.spectralRadius_eq_nnnorm` for self-adjoint `S`, together
with positivity of that shifted spectrum, gives `‖S‖ ≤ m + c`; then
`abs_re_inner_le_norm` applied to `S x`, minus `m * ‖x‖ ^ 2`, is the claim.

**The seam is the third step, and it is the reason a norm bound will not do.**
`spectralRadius` records *absolute values*, so the argument has to use the
positivity of the shifted spectrum explicitly before it can convert the
spectral-radius supremum into the upper endpoint `c`.  A bound of the form
`‖A‖ ≤ c` loses exactly that sign information and is insufficient.

Downstream real results reduce to this single theorem, so it should not be
replaced by an opaque real-spectrum definition.
-/

public section

namespace TauCeti
namespace SpectralOrder
namespace Real

open TauCeti
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

                                                                          

                                                                               
                                            

                                            
                                                                             
                                     
                                                                          
                                                                         
                                                                    

                                                                               
                                                                       
                                                                            
                                                                                
                                                                       
              
                                                                                          
                                                                               
                                                               
                                                                                     
                                                                                   
                                                                                       
                                                                                        
                                                                              
                                                   
                                                
                                     
                                
                                                  
             
                                            
             
                              
                                                             
                               
                                                            
                                
                                                              
                                                                  
                                                           
              
                                              
                                                        
                                    
            
                                                              
                                
                               
                                            
               
                               
                           
                                                                          
                                                     
                                                  
                    
                                                
                                          
                                 
          
                          
                                                                  
                                                    
              
                                          
                                     
                           
                     
            
                                                                      
                                                        
                                 
                                                                    
                         
                                    
                                       
                                           
                                                            
                                                                  
                        
                                                                         
             
                                                
                       
                                  
                                                               
                                             
                                     
           
                                    
           
                                         
                                                           
                                                  
                                 
        
                                                    
                                                           
                              
                                                                    
                                     
                                                                     
                                                            
                                      
                                                                                    
                                                                                    
                                                     
                  
          

                                                                          

                                                                           
                                      
                                                   
                                                
                                     
                                
                                     
             
                                    
                                         
                                                   
              
                                      
                           
                                      
                                        
                               
                           
                                
             
                                                                             
            
                         
                                                       
          

                                                                          
                                                                             
                           
                                                           
                                        
                                                   
                                   
                                                   
                                
                          
                                                                                    
                                            
                                                                        
                                                          
                           
            
                                                
                                                
         

                                                                          
                                                                             
                           
                                                           
                                        
                                                   
                                   
                                                   
                                
                          
                                                                                    
                                            
                                                                        
                                                          
                           
            
                                                
                                                
         

                                                                     
                                                                               
                                         
                                                           
                                                               
                                                     
                               
                                         
                          
                                                           
                                                     
                                                           
                                                       
                                                                           
                                                                           
                                                                          
                                                                          
                                                                          
                                                                          

end Real
end SpectralOrder
end TauCeti
