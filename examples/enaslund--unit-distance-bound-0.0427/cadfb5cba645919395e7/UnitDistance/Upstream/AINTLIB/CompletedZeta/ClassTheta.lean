/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
Modified for enaslund/unit-distance-bound: import lines relocated from
DedekindResidue.* to UnitDistance.Upstream.AINTLIB.* and `public import Mathlib`
narrowed to specific Mathlib modules for the Lean 4.32.0 / Mathlib 81a5d257 pin;
proof text unchanged. Upstream and local hashes: third-party/aintlib/manifest.json.
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.Tactic
public import UnitDistance.Upstream.AINTLIB.CompletedZeta.HeckeTheta

/-!
# The normalised class theta and its clean functional equation  (SP1-AGE-4, bricks 2–3)

The unit-averaged Hecke theta `heckeG I t` of `HeckeTheta.lean` depends on the ideal `I`,
not just its class: `g_{x·I}(t) = g_I(|N(x)|²·t)` (`heckeG_principal_mul`). Normalising the
ray parameter by `N(I)⁻²·β` with `β = 4^{r₂}/|Δ_K|` kills that dependence:

* `heckeGClass C x` — the **normalised class theta** `Ĝ_C(x) = g_I(N(I)⁻²·β·x)`, attached
  to an ideal class `C` through any representative (`heckeGClass_eq`);
* `heckeGClass_inversion` — the **clean Hecke symmetry** `Ĝ_C(1/x) = √x·Ĝ_{C^∨}(x)`, where
  `C^∨ = [𝔡_K⁻¹]·C⁻¹` is the trace-dual class: with this `β` the covolume, norm and
  `4^{2r₂}` factors of `heckeG_inversion` cancel to **exactly 1**;
* `heckeF x = ∑_C Ĝ_C(x)` — the total theta, with `heckeF_inversion : f(1/x) = √x·f(x)`,
  the input to mathlib's abstract functional-equation machinery (`WeakFEPair`, weight
  `k = 1/2`, root number `ε = 1`) producing the completed Dedekind zeta function.

Supporting material: the general fraction-field version of `ClassGroup.mk_eq_mk`
(`classGroup_mk_eq_mk_iff`), the real ideal norm `idealNormR` and its behaviour under
principal rescaling and trace duality, and the class-group bijection `dualClass`.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open FractionalIdeal (spanSingleton)
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]


                                                                                     
                                                                                    
                                   
                                                                     
                                         
                                                          
             
           
                                                 
                                              
                                                                
                           
                
                                                                                 
                                                
                                                      
                                                                            
                                                                
                                                                        
                                
                                                                            
                                                
                                                    
                                                                                      
                                                                       
                                                
                                                                 
                   
                
                                                                    
                                   
                                                                                        
                    

                                                                                           
                                                        
                                                                    
                                              
                                     
                                                     

                                                                
                                                                     
                                                                    

                                                                
                                                                    
                                                                  
                                                                            
                                                                                  
                                     

                                                                                   
                               
                                                         
                                        

                                                                             
                                                 
                                                                   
                                                                           
                                                         

                                                           
                                                                                 

                                                                 
                           
                                                                            

                                             
                
                            
            

                        
                                                                                           
                                                                         
                                                                      
                                                         
                                                                   
                                                     
                               
                                  
                                                                           
         
                                                          
                                      
                                                        
            

                        
                                                                                   
                                                                                  
                                                              

                                                                                     
                                  
                                                 

                        
                                                                                        
                                                                      
                                                                   
                         
                                                           

                        
                                                                               
                                                      
                                                                                   
                  
                                                                     

                                                                    
                                                                    
                                                     
                                     
                                                                
                                                                   
                                                                          
                                 
                                                                   

                                                    
                                                                        
                                           

                                                            
                                                                               
                                                            

                                                              
                                                                    
                                                                                                
            
                    
           
                                             
                                                                    

                        
                                                                    
                                    
                                                             
                                                    
           
      

                        
                                                               
                                                                                       
               
                                                                           
                                                                                 
                                               
                            
                               
                                                                     
                                                     
                                                    
                           
                                                                       
                                                            
                                             
                                                                         
                                                                                     
                                            
              
        
         
                                                              
                                                                
                                                             
                                                                   
                                                                                  
                    
                                                                                         
                                                                             
                                                      
                                                                         
                                               
                                                            
                                                                                     
              
                
                                                                                   
                                                              
            
                                                                                        
                                                                              
            
                                                                            
                  
            
                                                                                               
                                                                                 

                        
                                                                                          
                                                                      
                                                                                 

                        
                                                                                   
                                                                   
                                               
                                                     
                                     
                                                                   
                                                                                      

end

end DedekindResidue
