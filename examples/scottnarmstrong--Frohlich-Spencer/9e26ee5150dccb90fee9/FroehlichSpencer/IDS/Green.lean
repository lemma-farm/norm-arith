/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Lattice.Kernel
public import FroehlichSpencer.Infra.Green.Existence
public import FroehlichSpencer.Infra.Green.InfiniteVolumeRegularity
public import FroehlichSpencer.Infra.Ergodic.Basic
public import FroehlichSpencer.Infra.Lattice.Basic
public import Mathlib
/-!
# The lattice Green function

The infinite-volume Green function `G(z; x, y)(v)` on `ℤ^ν`, the unique square-summable solution of
`(-Δ + v - z) ψ = δ_y`, obtained from the generic theorem for `hoppingKernel ν` with potential
`v + 2ν`.

We prove the characterization, the bound `|G| ≤ 1/|Im z|`, shift covariance,
measurability in `v`, Combes–Thomas decay and the large-`t` asymptotics `it · G(it; y, y) → -1`.

Motivation: Fröhlich–Spencer (1983), (1.4), Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology

namespace FroehlichSpencer.IDS

                                                                                  
                                                                                                 
                                       
                                                                                     
                       
                                                                                       
                                                                                      
        

                                                                                         
                                                                                              
                                                                    
                                            
                                 
                                                                                         
                                                                                          
            
                           
        
                                                                                           
                                                                                         

                                                                                     
                                     
                                                                                           
                                       
                               
                                                                                     
                                                                                   
                              

                                                                                              
                                            
                                                                                    
                                                                                              
                                  

                                                                
                                                               
                      
         
                                           
                                                                                       
                                     
                                                                                       
                                         
                    

                                                                                              
                                                                                            
                                                                         
                                                
                                       
                                                                                          
                            
                                                           
                                                                        
                                                          
                                                                                
                                                                              
                                         
                                                                 
                  
                                                                                                 
                              
                  
                                               
                      

                                                                                
                                                                 
                                                                                                 
                                        
                                                                                
                                                         
                                                                             
                                                                          
                                                                   
                    
                                      

                                                                                   
                                   
                                                                         
                                                         
                                                                                        
          
                           
                                                                                        
          
                           

                                                                                 
                    
                                           
                                                                  
                                                                       
                                                                                
                                 
                                                                                 
                                                                  
                                                                                            
                                                                                               

                                                                        
                                                                                                
                                                        
                                
                                                                             
              
                                                           
                                                                              
                                                               
                                            
                                      
                                                        
                                                                       
                                                                               
                                                           
                    
                                       
                                                                                 
                                                                                         
                                           
                                                                                   
                                                                                           
                                       
                                    
                                                                                        
                                      
                                         
                                                                                     
                           
            
                                     
                                                                                     
                                                        
                                               
                                                           
                        
                                                                          
                                   
                                                         
                                           
                                        
                                                                   
                                                               

end FroehlichSpencer.IDS
