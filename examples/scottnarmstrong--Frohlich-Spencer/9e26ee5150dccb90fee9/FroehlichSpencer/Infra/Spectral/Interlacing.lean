/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Monotonicity
public import Mathlib
/-!
# Finite-rank interlacing of eigenvalue counts

A perturbation of rank `≤ r` changes the eigenvalue counts by at most `r`; for a one-site
diagonal change the counts differ by at most one and move monotonically (Fröhlich–Spencer (1983),
Appendix C, Fröhlich–Spencer (1983) line 1821: "the eigenvalues … are interlaced, hence
`0 ≤ δ_j N ≤ 1`", with `δ_j N` defined in (C.3)).

`eigenvalueCount_update_le` is that statement for
an arbitrary matrix plus a diagonal potential.
-/

@[expose] public section

open Matrix Finset ComplexOrder

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}

                       
                                                           
                                                                                
                                                             
                                                 
                    
       

                                                                                         
                                                                      
                                                   
                                                                  
                                           
                                                                                         
                                                                                          
                                                                          
                                              
                                                                                                 
                                                          
                           
                                      
                                      
           
                                                                         
       

                                                                                           
                                                                          
                                                   
                                                                  
                                           
                                                                                         
                                                                                          
                                                                          
                                              
                                                                                                   
                                                                
                           
                                      
                                      
           
                                                                             
       

                                                                              
                
                    
                                                        
           
        
                                

                                                                                     
                                              
                                                      
                                                            
                                                 
                                                 
                          
       

                                                                                       
                                              
                                                          
                                                                
                                                   
                                                   
                          
       

                                                                            
                                                                                
                                                                                           
                                                    
                            
                                                   
                                                                                  
       

                                                 
                                                                 
                                                         
                                                                 
           
                                                                                        
                                              
           
                                                      

                                                                                       
                                                                     
                                                      
                                                         
                                          
                                                                      

                   
                                                             
                                                                   
                                                         
                                                                  
           
                                                                      
                                              
                   
           
                                               
                                       

                                                                                            
                                                                     
                                                  
                                                            
                                                       
                                                                
                          
                                   

                   
                                                                                 
                                                           
                                                               
                                                 
                
         
         
                                                                                      
                          
           
                                                           
                  
                  
        
                  
        

                                                                                                
                                                                              
                                                                                        
                                                 
                                                           
                                              
                                                                       
                                                                  
                                         
                                                                          

                                                                                    
                 
                                                                              
                                                                                        
                                                     
                                                               
                                              
                                                                       
                                                                  
                                           
                                                         
                                                                 
                            
                                                       
                            
                                     

end FroehlichSpencer.Infra
