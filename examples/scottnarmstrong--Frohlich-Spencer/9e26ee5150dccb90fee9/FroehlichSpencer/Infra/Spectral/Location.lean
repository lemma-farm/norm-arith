/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.Count
public import FroehlichSpencer.Infra.Spectral.QuadForm
import Mathlib

/-!
# Location of the spectrum of a diagonal perturbation

For `A : Matrix ι ι ℂ` and a real potential `v : ι → ℝ`, the eigenvalues of the Hermitian matrix
`A + diagonal v` lie in `[a - ‖A‖, b + ‖A‖]` when `v` takes values in `[a, b]` (operator-norm
form), and each lies within the Gershgorin row-sum radius of some `v k + Re (A k k)`.

Counting
corollaries: no eigenvalue `≤ E` above the potential level `E + ‖A‖`, and all eigenvalues `≤ E`
below the level `E - ‖A‖`.

This is the first-order spectral location used in
Fröhlich–Spencer (1983), Fröhlich–Spencer (1983); nothing here is lattice specific.
-/

@[expose] public section

open Matrix Finset
open scoped Matrix.Norms.L2Operator

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

                                                                                                  
                                                                            
                     
      

                                                               
                                                                                    
                                                                                        
                                                                  
                                                   
                                                                                    
                                                              
                                                                                      
                                                 
                           
                                     
                                                              
                                           
                                                                  
                                                                                      
                                           
                                  
                                                                                 
                                              
                      
             
                                           

                                                    
                                                                                       
                                                                                   
                                                                                    
                                                                                              
                                                             
                                          
                                   
             
                                                           
                    
                  
                                           
                
                                                
                                                                                            
                                                                 
                                
                                                     

                                                                                 
                                                                    
                                                                                           
                                                      
                
                                                                                 
                   
                                                                                
                                                
                                       
                                                           
                                  
                    

                                                                            
                                                                              
                                                                                              
                                  
                                                         
           
                                                                 
                                                                               
                                                                                                
                                                                       
             
          

                                                                                  
                                                                              
                                                                                              
                                               
                                                     
           
                                                                 
                                                                                        
                                                     
          

                                                                               
                                                                       
                                                                  
                                       
                                                                        
                                    
                                                      
                                                                       
                                           

end FroehlichSpencer.Infra
