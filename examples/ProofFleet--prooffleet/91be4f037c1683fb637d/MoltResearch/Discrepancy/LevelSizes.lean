import MoltResearch.Discrepancy.WindowAssembly
                                            

/-!
# The level polynomials' sizes, in schedule terms (Track R, A2-III, M-3)

`BandCapstone.setIntegral_norm_sq_level_sum_of_prev_large_le` and
`BandSchedule.levelJ_le_budget` are stated with two abstract sizes: `small v`,
a pointwise bound on the current level's cell polynomial on `G`, and `large`, a
pointwise lower bound on the previous level's prime polynomial there.
`WindowTK.band_energy_level_le_of_prev_large` records what the schedule supplies
for them — `small v = e^{−αv/(2N)}` and `large = e^{−βr/(2N_prev)}`, the
`e`-adic ladder factors at the cell index — and leaves the instantiation to the
consumer.  This module is that instantiation, and it is the fourth of the
schedule's abstract quantities to be bound after the cell mass, the level total
(`PrimeMassCell`) and the cell count (`BandSchedule.cellCount_le`).

**The finding: the level-`j` total smallness needs no new schedule input.**
`levelJ_le_budget` consumes the sizes through `S₁ = ∑_v (small v)²`, and at the
schedule's `small` that sum is a geometric series in the `e`-adic index at rate
`2α` — *the same series, at the same rate, from the same level bottom* that the
level-one leg already pays as its smallness gain.  So
`levelSmallness_total_le`'s right-hand side is literally the middle factor of
`levelOne_le_budget`'s `hfitP`, and a schedule that affords the level-one leg
affords this one on the same arithmetic.  Nothing here is new analysis; both
lemmas are the `e`-adic index bounds of S-cal-2 read at the level-`j` seam.

Note the direction each size is bounded in.  `small` enters `levelJ_le_budget`
multiplied, so it needs an **upper** bound and `eadic_level_bot_exp_le` supplies
it from the level's bottom `P`.  `large` enters *divided* — the level-`j`
estimate pays `1/large^{2ℓ}` for inserting `ℓ` copies of the previous level's
polynomial — so it needs a **lower** bound, and that is
`eadic_level_top_exp_le` read as a reciprocal, priced by the previous level's
top `Q`.
-/

namespace MoltResearch

open Finset

                                                              

                                                                          
                                                                         
                         

                                                                      
                                                                            
                                                                            
                                                                      
                                                                              
                                                       

                                                                             
                                                                             
                                          
                                                                    
                              
                                                      
                                 
                                                           
                                                             
                                                   
                                  
                                                                         
                                                                      
                                                                         
                                                               
           
                           
           
        
                                                                                   
                                                                                 
                                    
                                                           
                                     
                                                              
                                             
                                                          
                                                     
                                                             
                                                
                                                

                                                                             
     

                                                                             
                                         
                                                                                
                                             

                                                                              
                                                                                
                                                                             
                                                            
                                                                        
                 

                                                                            
                                                                                
                                                           
                                                                          
                               
                                                  
                                                  
                                                           
                                              
                                
                       
                                         
                                                     
            
                                                                          
                                                         
                                                               
                                 
                                            
                                                
                                         
                                                          
                                                   
                                                                
                                                           
                                                            
                                                                      
                                                           
                                                            
                                     
                
                                                        

                                                                              
     

                                                                       
                                                                          
                                                                               
                                                                             
                                                                          
                                                                              
                                 

                                                                               
                                                                               
                                       

                                                                             
                                                                    
                                                                            
                                                                            
                                                                         
                                       
                                                                             
                                                         
                                                    
                                                
                                                    
                                                         
                                                                 
                                                  
                                          
                                
                                       
                                       
                                                                                 
                       
                                   
                                                                             
                                               
                                                                         
                                                                          
                                                                              
              
                                                                             
                                                                                
                                                         
                                                                  
                                                    
                                                                      
                                                          
                                          
                                                                                   
                
                                                                                 
        

end MoltResearch
