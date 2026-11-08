/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
                                            
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Pointwise weak gradients on a set

## Main declarations

* `EllipticPdes.Embedding.HasWeakGradOn`: the weak gradient of a function on a set.
* `EllipticPdes.Embedding.HasWeakDerivAlong`: the weak derivative along a direction of any normed
  space.
* `EllipticPdes.Embedding.hasWeakGradOn_iff`: a weak gradient is a family of weak derivatives.
* `EllipticPdes.Embedding.HasWeakDerivAlong.comp_affine`: transport through `x ↦ e x + c`.
* `EllipticPdes.Embedding.HasWeakDerivAlong.sum`: a weak derivative is linear in the direction.

The `Lᵖ`-scale, pointwise-function analogue of `HasWeakDerivOn`: a function `u` has weak
gradient `g = (gₖ)` on `B` when the integration by parts identity is satisfied against every
smooth test function supported in `B`. This is the interface the Morrey embedding consumes; it is
stated for functions (not `Lp` classes) and for a full gradient tuple so that a
general exponent `p > d` is expressible, which the `L²`-only `HasWeakDerivOn` cannot do.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

                                                                                         
                                                                                            
                                       
                                                                     
                                                                                           
                                                                                    
                                                                                          
                                                                             

                                                                                
                                                                                      
                                                                                 
                                                    
                                                      
                                                                                           
                                                                                   
                                 
                                                              

                                         

                                                                                                 
                                                                                              
                                                                                              
                                                                                       
                                       
                                                                         

                                                                
                                                                    
                                    
                                                                       
                                          
       
                                                                                  

                                                                                
                                                                                                   
                                                                                        
                                                              

                                                                     
       
                                                                       
                                                
                                                               
                

                                                                          
                                                                       
                                                                           
                                 
                                                                    

                                                                    
                                                                                      
                                                                             
                                   
                                                        

                                                                                               
                                         
                                                                    
                                                                                         
                               
                                                                   
                        
                              
                       
                                                         

                                                                                               
                                                                                              
                  
                                                              
                                                                                     
                                                                 
                                                                                   
                                                           
                                                                         
                        
                                              
                                          
                                                                
                                                  
                                                                
                                                         
                                                          
                                                  
                                                                               
                                                            
                                            
                                                                          
                                           
                                                             
                                                                  
                                                  
                                                                          
                                                       
      

                                         
                                                                 
                                                                 
                 
      

                                                                                     
                                                         
                                                          
                                                                               
                                                  
                                               
                                                      
                                                
                                                                                 
           
                                            
                                                    
                       
                                                                  
                                        
                                                                         
                                        
                                                                  
                                       
                                                                 
                                                  
                                            
                                           
                                                                   
                                                      
                                                                              
                        
                                           

                                                                                      
          
                                                                                          
                                                                                 
                                                                                

                                                                                          
              
                                                                              
                                                                                     
                             
                                                                               
                                               
                                                     
                                                                           

                                                                                        
                                       
                                                                           
                                                                                     
                                                                           
                                                                          
                                                                                                

section WeakDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

                                                                                             
                                                                                     
                                                                                 
                                                                             
                                                               

                                                                                     
                                                                      
                                                                                   
                         
                                                                                  
                                                                              

                                                   
                                                                
                                               
                                                            
                  
                                                                                    
                                           
                           
                                                                    

                                                                                       
                                                                                       
               
                                                                                 
                                                                                             
                                                                                               
                                                                                      
                  
                                          
                                                               
                                                               
                                                                                  
                                                                   
                                                                            
                                             
                                                                
                                                                  
                                                       
                                                                  
                                                                
                                                   
                  
                                                                
                                
                                                     
                                                     
                                                                                          
                         
                                                   
                  
                                                                    
                                
                                       
                                                                           

                                                                                       
                                                                                               
                                                               
                                                                            
                                                                                      
                                           
                                                                           
                                  
                  
                                                                     
                                                     
                                                                     
                                                                                   
                                     
                                     
                                                         
                                                                              
                                                                            
        
                                                                
                                 
              
                           
                        
                                                      
                                                                      
                                                                  
                        
                      

                                                                        
                                                                    
                                                                     
                                           
                                                                               
                                                    

                         
                                                                                           
               
                                                                                      
                                                                  
                                                                    
                                                                         
                                 

                                                                                         
                                                                          
                                 
                                                                                 
                                                               
                                           
                                                                                     
                                        

                                                                                               
                                                                             
                                     
                                                                                     
                                                                          
                                      
                                                                          
                                                             
                                              

                                                                                        
                                                                                           
                                                                                  
                                                                             
                                                                        
                                                                  
                                                                                       
                                                              
                                                      

end WeakDeriv

                                                                                           
                                                                                             
                                                                                             
                                                                                              
                                                                                 
                                                                                          
                                                                     
           
                                                                                                  
                                  
                                                                                               
                                                             

                                                                                    
                                                                           

                                                                   
                                                                    
                                                    
                                                             
                                  
                                                
                                                 

end EllipticPdes.Embedding
