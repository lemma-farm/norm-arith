/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import Mathlib
/-!
# Real-valued view of a canonical symmetric ideal family

`TauCeti.SymmetricOperatorIdealFamily` stores its gauge in `ℝ≥0∞`, extended by `∞`
off the ideal.  That is the right presentation for the library: it makes the gauge
total, gives the structure an `ext` lemma, and is what a Mathlib-bound development
wants.  The Davis--Kahan estimates, by contrast, are stated and proved in `ℝ` — the
paper's constants are real, and the proofs run on `linarith`, `nlinarith` and
`mul_le_mul_of_nonneg_*`, none of which work over `ℝ≥0∞`.

This file supplies the missing `ℝ` view, so that migrating a theorem off the
historical free-data record — a membership predicate plus a real gauge, since
retired — is a **retype and not a re-proof**.

## Why this file exists at all

Phase C of the §13.2 migration was released three times without being started, and
the recorded reason each time was that it is "a re-proof over a differently-valued
gauge": every conclusion changes type from `ℝ` to `ℝ≥0∞`, `gauge_nonneg` goes
vacuous, `∞` cases appear, and Neumann summability in `ℝ` and in `ℝ≥0∞` are
different theorems.

All of that is true, and all of it is about a question the lane does not have to
answer.  *Which structure parameterizes a theorem* and *which numeric type its
estimate lives in* are separable, and they had been conflated because the canonical
family had no `ℝ` view to migrate onto — only `KyFanDominantIdealFamily` had one,
and that structure is strictly stronger, so retyping onto it would weaken every
theorem it touched.  With the view below, the 18 remaining legacy-binder modules
change their binder and keep their proofs; restating the estimates in `ℝ≥0∞` becomes
a separate and genuinely optional decision.

## Where the `ℝ≥0∞` arithmetic lives

Phase C stated every lemma here over `gaugeReal`/`Mem` but *proved* it through the
historical record, so that retyping the tree cost no proof work.  Phase D paid that debt: every proof below now runs on the canonical laws
directly, and this file no longer imports the adapter.

The design point is where the bill landed.  Turning an `ℝ≥0∞` law into an `ℝ` one needs
a finiteness side condition at each step -- `ENNReal.toReal_mono` wants the larger side
finite, `toReal_add` wants both summands finite -- and that reasoning appears **in this
file only**, not at the 117 call sites across 30 modules that a direct migration would
have had to re-prove.  Every `Mem` hypothesis below is exactly the finiteness those
conversions consume.

Completeness is the one law that genuinely needs `IsComplete`, so that instance is
assumed on `gaugeReal_complete` alone rather than on the section; the other laws hold
for any canonical symmetric family.
-/

open scoped ENNReal

namespace TauCeti

namespace SymmetricOperatorIdealFamily

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)


/-- Membership in the ideal: the gauge is finite.

The same predicate as `OperatorIdealFamily.carrier`, spelled as the `Mem` the
Davis--Kahan statements are written against. -/
abbrev Mem (A : E →L[𝕜] F) : Prop :=
  N.toOperatorIdealFamily.gauge A ≠ ∞

                                                                                 
                                                                                 
                                                 
                                                     
                                          

                                                            
                                             
                                                            

                                                                 
                                             
                                                                   

                                 

                                             
                                           
                                          

                                        
theorem add_mem {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) : N.Mem (A + B) :=
  N.toOperatorIdealFamily.carrier.add_mem hA hB

/-- Ideals are closed under scalar multiplication. -/
theorem smul_mem (c : 𝕜) {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem (c • A) :=
  N.toOperatorIdealFamily.carrier.smul_mem _ hA

                                                  
                                                                       
                          

                                                                     
                                                                                 
                          
                                                 

                                                
                                                                               
                       

                                        
                                                              
                  

                                                   
                                                        
                                      
                                       
                                                            

                                                
                                                                          
                                                             
                                                                    
                               
                                                             
                                              

                                                           
                                                                
                                                   
                                               
                                                                         

                                           
                                                           
                                               
                                                                

                                      
                                                                         
                    
                                                               
                                                            
                                                                  
                                                                  
                                                      
                                                                         

                                                                   
                                                                                      
                                                                             
                         

                                                                        
                                                 
                                                               
                                                 
                                                           
                                    
                                                     
                                     
                                                                       
                                                                                       
                                                                                          
                                                                      
                                                 
                                                                                            
                                                                      
             
                                                            
                                                     
                              
                             
              
                                  
                                                                 
                                                     
                                           
                                 
                           
                            
                 
                                                                                             
                         

                       

                                        
theorem neg_mem {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem (-A) := by
  simpa using N.smul_mem (-1 : 𝕜) hA

                                               
                                                      
                                          
                                          

                                                                      
                                                                      
                        
                                                          

                                                                        
                                                                                   
                                                    
                                                                    
      
                        
                                                                       
                                                                  
                                  
                               
                                                          
                                                            
                                      

                                                                     
                                                              
                                   
                                              
      
                                                                                   
                                                                                  
                                  

                                                                       
                                                                       
                        
                                                          

                                                                         
                                                                                    
                                                    
                                                                    
                                                
                                                    
      
                        
                                                                         
                                                                  
                                    
                                
                                                                
                       
                                      

                                                                      
                                                               
                                   
                                              
                                                                    
                                       
      
                        
                                                                         
                                                                  
                                   
            
                                            
                                

                                                                         
                                                                         
                                                                  
                                                   
                                       
      
                                                            
                                
                                          
                                

                                           
theorem sub_mem {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) : N.Mem (A - B) := by
  rw [sub_eq_add_neg]
  exact N.add_mem hA (N.neg_mem hB)

                                                     
                                                                          
                                                             
                     
      
                                                              
                                          
                                                                   

                                                       
                                                              
                                   
                                     
            
                        

                                                             

                                                                                          
                                                                                          
                                                                                       
                                                                           

                                                                                        
                                                                   
                                                                           
                              
                                                                     
                              
                                                                                  
            
                                                         
                                 
                                
                                     
        
                                              
                                                     
                           
                                                                        
                                                     
                                                        
              
                                     
        
                                              
                                                     
                           

variable {ι : Type*}

                                           
                                                         
                                                            
           
                                            
                 
                        
                               
                                                         
                                                           

                                                                     
                                                                  
                                 
                                                                 
           
                                            
                                    
                        
                                                     
                               
                                           
                                                                                    
                                                                                 

                                   

                                                          

                                                                                          
                                                                               
                                                                                        
                                                                                          
                                  
                                                
                                                                       
                                                                              
                                                              
                                      
                                                                                 
                       
      
                                     
                                             
                                                            
                                                     
                                                                                
                                                                     
                                                                  
                                                                        
                                                         
                                                                 

                                                                            

                                                                                           
                                                                           
                                                                                        
                                                                                        
                                                                                         
                                                                      
                                                                  
                                                                       
                             
                                                                         
                                                                     
                                                                     
                                                                       
                                     
                                                                  
                               
                 
      
                                           
                                                    
                                                                     
                                                                           

                                                                              
                                                                                  
                                                        
                                             
                                                                      
                               
                    

                                                                       
                                                              
                                                         
                                                                  

end SymmetricOperatorIdealFamily

end TauCeti
