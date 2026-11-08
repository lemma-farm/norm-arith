/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.MinMax
public import FroehlichSpencer.Infra.Spectral.Sorted
public import FroehlichSpencer.Infra.Spectral.QuadForm
public import Mathlib

/-!
# Shift invariance and Loewner monotonicity of eigenvalue counts

Shift invariance `N(E, H + t) = N(E - t, H)` (Fröhlich–Spencer (1983), Appendix C uses
`N(E, v) = N(0, v - E)`) and monotonicity of the counting functions and sorted eigenvalues under
positive semidefinite perturbations; in particular raising a diagonal potential lowers the counts.
-/

@[expose] public section

open Matrix Finset ComplexOrder

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}

                                                                 
                                                              
                                                            
                                                     
                                                                      
                                                                                           
                                                              
                                                                          
         
                                                                                     
                                                                          
                                                 
           
                                             

                                                                   
                                                              
                                                                
                                                       
                                                                      
                      
                                                                                    
                                                              
                                                                                  
         
                                                         
                                                        
                                                                          
                                                 
           
                                               

                                                                
                                                                                 
                                                        
                          
                                                                               
                                                                    
                                                                                  
                                                                   
                     

   
                                                                                      
                                                                      
  
                                                                              
                                                          
                                                                       
                                                      
                                                           
                                                                           
           
                        
               
                                              
          
                
                                                                                            
              
                                                                                   
      

                                                                                    
                                       
                                                      
                                           
                                                       
                                                                            
                                                    
                                    
                                           
                                          
                        

                                                                                      
                                       
                                                          
                                           
                                                             
                                                                                
                                                    
                                    
                                           
                                          
                        

                                                                                   
                                                          
                                                 
                                                                                              

                   
                                                                                    
                                                                                                
                                                                                    
                                                     
                                
           
                        
               
          
                
           
                                               
                   

                                                                
                                                                                            
                                                          
                                                                    
                                                  
                                                                              

                                                                                
                                                                        
                                                                    
                                                      
                                                                                

end FroehlichSpencer.Infra
