import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.ParsevalBridge

/-!
# The regime split with the low band left as an energy (Track R, A2-III)

`integral_norm_sq_sum_translates_regime_split` (the harness's three-regime
split) prices the frequency line in three pieces: an explicit low-band energy
`∫_{|ξ|<K} ‖P‖²‖𝓕F‖²`, a middle piece `Mmid²·∫‖𝓕F‖²` controlled by the
**pointwise sup** of the phase polynomial on `K ≤ |ξ| ≤ L`, and a tail
controlled by `Mtot²/L²`.

**That middle piece is the trivial bound on the band energy it stands for**,
and it is exactly the quantity the `[mrt]` A.2 band campaign exists to improve:
`Mmid²·∫‖𝓕F‖²` is sup² × window mass, whereas the campaign's capstone
(`band_energy_le_budget`) delivers the honest `∫_band ‖P‖²·w ≤ 𝔅`.  A sup slot
cannot consume an energy bound, so the campaign's output does not compose with
its own consumer.

This module supplies the missing shape.  Rather than a four-way split it uses
**two regimes**: everything below `L` is left as an integral, and only the tail
is collapsed.  The consumer then splits `{|ξ| ≤ L}` into whatever bands it
wants — the low band `|ξ| < K` and the mid band `K ≤ |ξ| ≤ L`, say — with
`setIntegral_le_sum_of_cover`, which already exists and takes an arbitrary
finite cover.  That is simpler than fixing the two-band structure here and
strictly more useful, since the band structure is the schedule's business and
varies with `J`.

The weight in the surviving integral is `‖𝓕 F‖²`, which is the capstone's
abstract `w`; when `F` is the slice window its sup is `(4H/A)²`
(`norm_fourier_slice_window_le`), which is the capstone's `Cw`.  The two sides
were designed to meet — only the slot was the wrong shape.

Kept in its own module because `PlancherelHarness` has twenty modules
downstream, `DyadicMVT` among them, which makes editing it the most expensive
change in the tree.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff

                                                                           

                                                                            
                                                                            
                                                                            

                                                                          
                                                                              
                                                                              
                                                             

                                                                               
                                                                         
                                                    
                                                                  
                                                      
                             
                    
                                                                               
                                       
                                  
                                                                             
                          
                                                         
           
                                                             
                                                              
                                                               
            
                           
                                                                     
                             
                                                                     
                                    
                                                  
                
                     
                                                                         
                                                            
            
                                                          
                                                              
                                                    
                                                          
                                                         
                            
                                                              
                                                           
                                                                
                     
                                                                        
                                      
                                                           
                                                    
                                                          
                                                                       
                                       
                                                                
                                                                    
                                            
                                                                       
                                            
                                                                         
                                                
                                             
                                                    
                                                        
                                  
                                                     
                 
                       
                                         
                                                           
                                                    
                                   
                
                                        
                                                          
                       
                                          
                                                          
                      
                                                                              
                                                                 
                                                 
                                                               
                                                       
             
                                                              
                                                      
              
                            
                                                    
                        
                       
              
                           
                                                                            
                                                  
                                                          
                                                           
                                                                              
                                       
                                        
                                 
                         
                                               
                
             
                                   
                                                               
                                                                         
                                              
                                         
                                                               
                     
                                                              
                                            
                                                  
               
              
              
                                                                          
                                                       
                                                

                                                                            

                                                                             
                                                                              
                           

                                                                                
                                                                             
                                                                           
                                                                            
                                                                        
                                                                            

                                                                             
                                                                          
                                                                
                                                                              
                                                
                                                                            
                 

                                                                     
                                                               
                                                  
                                           
                                                                     
                                  
                    
                                        
                                                                            
                                   
                                                   
                                                
                                                   
                                            
                                         
                                  
                                              
                                                                            
                                                               
                                         
           
                                                                  
                                                  
                                  
                                  
                                                            
                                                           
                                                          
                                                               
                                                       
                                                               
                                               
           
                                                         
                                              
                  
                          
                                       
           
                                                           
                                                               
                                                               
                                                    
                 
               
          
                    
              
                                                    
                                                                  
                                                     
                                                              
                                                           
             
                                                                             
                                            
                                                        
                                       
                                                        
                                                        
                  


end ExpSums

end MoltResearch
