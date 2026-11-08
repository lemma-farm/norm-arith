-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Sobolev.Ambient.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Group.Real

/-!
# Local integrability and continuity of translated-kernel integrals

Let `k` be a continuous kernel whose support lies in the closed ball of radius
`ε` about the origin, so that `k (· - y)` is supported in the closed ball of
radius `ε` about `y`. For a function `g` that is locally integrable on an open
set `Ω`, the product `x ↦ g x * k (x - y)` is then integrable as soon as the
ball `closedBall y ε` sits inside `Ω`, and the parametrised integral
`y ↦ ∫ x, g x * k (x - y)` is continuous wherever the translated ball still
fits inside `Ω`. These are the local-integrability and continuity inputs used
in the Caffarelli–Kohn–Nirenberg paper (CKN) when a spatially localised kernel
is slid against a locally integrable density.
-/

namespace CKN

open MeasureTheory Metric Filter

set_option autoImplicit false

noncomputable section

                                                                              
                                                                          
                                                                          
                                                                         
                                                                             
                                                                           
                                                               
                                                                                 
                                                             
                    
                                                         
                                  
                                                                                   
                             
                                                                     
                              
                 
                                                        
                                                     
                                            
                                                  
             
                                  
                                                                   
                   
                                                  
           
                      

                                                                       
                                                                               
                                                                               
                                                                           
                                                                             
                                                                            
                                        
                                                                            
                                                                     
                               
                                             
                                                  
                                                                                  
                                                                                        
              
                                   
                              
                  
                       
                                                                                    
                                                                    
                                                                                           
                                                                
                                                                            
                                                               
                                                                                     

                                                                              
                                                                               
                                                                   
                                                                               
                                                                             
                                                                 
                                                                                     
                     
                                                                     
                               
                                             
                                                     
                                                                               
                                                                            
                                                                              
                                                                         
                                                                            
                           
                   
                                                                                             
                                                                                        
                                         
           
                                                             
                   
                              
                                                                        
                                                 
                                  
                
                  
                                                                                  
                                        
                                            
                                                                                
                                                                    
                                                                                 
                                                                  
                                                
                                                                                
                                                                  
                         
                                           
                                                                   
                                             
                                                
                  
                             
                                         
                                  
                                                              
                
                                                  
                          
                                     
                                                 
                                        
                         
                                                                                       

end

end CKN
