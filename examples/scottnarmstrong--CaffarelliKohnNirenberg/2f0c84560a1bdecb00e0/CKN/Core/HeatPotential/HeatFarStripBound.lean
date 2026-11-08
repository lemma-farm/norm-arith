-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelCrossZero
import CKN.Foundation.Parabolic.Morrey.StripMass

/-!
# The causal thin-strip estimate on a far shell

Fix a degree-one Fourier multiplier `σ`, a base point `z`, a radius `r` and a
far shell index `j ≥ 6`, and two observation points `w, w'` in the ball of
radius `r` around `z` with `w.2 ≤ w'.2`.  The two causal kernels
`spatialMultiplierHeatKernel σ (w.1 - ·) (w.2 - ·)` and
`spatialMultiplierHeatKernel σ (w'.1 - ·) (w'.2 - ·)` differ, on the moving
time strip `{v | w.2 ≤ v.2 ∧ v.2 < w'.2}`, by the later kernel alone: the
earlier one vanishes there.  The strip's contribution to the far shell must
therefore be estimated on its own, with a factor that tends to zero as
`parabolicDist w w'` does.

That is what this module proves.  Two facts combine:

* on the far shell the two points are separated in **space**, because their
  time separation is at most `2 r ^ 2` while the shell sits at parabolic
  distance at least `2 ^ j r ≥ 64 r`; so the all-time order-four kernel size
  estimate applies with gauge at least `(2 ^ j r) / 2`;
* the strip is a thin time slab of width `w'.2 - w.2` inside a spatial ball
  of radius `2 ^ (j+1) r`, so the strip mass estimate
  `stripAbsLintegral_le_morreyNorm` applies with
  `d = 2 √(w'.2 - w.2)`.

Multiplying the two gives `(2 ^ j r) ^ (-1) √(w'.2 - w.2) ^ (2 - 5/θ)`, which
is at most `parabolicDist w w' * (2 ^ j r) ^ (-5/θ)` because
`√(w'.2 - w.2) ≤ 2 ^ j r` and `θ > 5`.

No hypothesis beyond the symbol class, measurability of the source and the
finiteness of its Morrey seminorm enters the statement.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean

                                                                  
                                                                        
                                                                    
          
                                                                          
                   
                                                           
                                    
                                                 
                                                                          
                                                                                 
                                     
                                                  
                                                                             
                        
            
                                               
                                 
                                                                           
                              
                               
               
            

                                                                           
                                                                         
                                                                             
                                                   
                                                                       
                                                                          
                                 
                                        
                                                             
                                     
                                                       
                    
                                 
                                                      
                                                               
                                    
                                                                     
                        
                                        
                                                                                    
                                                       
                                                  
                                                                       
                                                             
                                                  
                                                               
                                                                        
                             
                                      
                                                    
                                               
                                                     
                           
                                                         
                                    
                                                                
                                           
                                             
                                         
                                                                            
          
                               
                                                               
                                                              
                                        
                                                                                  
                                
                          
                                     
                              
                                                             
                                                                               
                                                                          
                                                
                                                   
                                    
                                                    
             
                              
                         
                                    
                                            
             
                              
                          
                                                  
                                                     
                                   
                                                        
                                     
                                                          
                                              
                                       
                                     
                                     
                                           
                                                   
                                                                 
                                      
           
                                                                                
               
              
                
              
                                                     
                                         
                
                                   
                          
                                                                  
                                         
                              
                                                  
                                                 
                                                                     
                                        
                                            
                               
                
                                                   
                                                    
                                                 
                                          
                                                            
                                                                       
                                                                  
                
                      
                                              
                                          
                                          
                                                                                 
                       
                                                                      
                                                           
             
                               
                                                                                 
                           
                                                                   
                                 
                
                      
                                              
                                   
                      
                                                          
                                         
                                                                            
                                       
                                                            
                                                     
                                                   
                                                      
              
                                                      
                                                   
                 
                                                  
                               
                                                                             
                                  
           
                                                                  
                           
                                                    
                     
                                                                                   
                                                     
                                              
                                                          
                                                   
                       
                                                                             
                                            
                    
                                                 
                                                       
                                                                 
                                                                               
                                                                         
                                                                      
                  
            
                                                                    
                                                      
                                                     
                                             
                                                                    
                                              
                                     
                                       
                
                                                   
                                                  
                                                                 
                                                                       
               
                                            
                                                       
                                                                   
                                                                                  
                                                     
                                                
                                                     
                
                                           
                                                                                        
                                                                  
                
                                                                      
                                                                    
                              
                                                         
                                
                                            
                                                                                
                             
                                                                
                                           
                     
                                                                                 
                        
                                                                      
                                                
                                                                     
                                       
                                             
                                                                      
                                        
                                                                       
                                                                      
                  
                          
                                                  
                                                                              
                                                                                    
                                                             
                                                              
                                                      
                                                                                  
                                
                              
                                                                            
                                                
                                                      
                                                
                                                              
                                                                
                                                
                            
                                                                             
                             
                                                 
                                                                       
                                            
                                              
                                  
                                      
                                                       
                      
                                                         
                                            
                             
                                                                     
                                                                    
                                                                     
                        
                                                            
                                         
                                                                        
                                               
                                                
                                                    
                                                              
                                                                       
                
                                                                        
                                                                               
                                                                              
                                                         
                              
                                                         
                                      
                               
                                                           
                                              
                                                  
                                                   
                                                   
                                                                  
                                           
                                
                    
              
                                                    
                                           
                                           
                                                       
                                                                     
                                           
                                           
                                                     
                                                                            
                                                     
                                                       
                
                                          
                                                  
                                               
                                  
                                
                                                                   
                                                

end CKN.Core.HeatPotential
