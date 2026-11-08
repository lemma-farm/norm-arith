/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialReversePoincare

/-!
# The tower of iterated-gradient energies of a polynomial

For a list `L` of polynomials write `sqSum L = ∑ p ∈ L, p ^ 2`, and `polyDerivs L` for the list of
all first partial derivatives of members of `L`.  The tower `derivTower f j` consists of all `j`-th
order partial derivatives of `f`, and `towerEnergy f j = sqSum (derivTower f j)` is the squared
norm of the `j`-th derivative tensor.

* `sum_sq_pderiv_sqSum_le`: the carré du champ of `sqSum L` is at most
  `4 (sqSum L) (sqSum (polyDerivs L))` (Cauchy--Schwarz);
* `gaussExp_sqSum_polyDerivs_le`: the reverse Poincaré inequality for a list of polynomials of
  degree at most `m`, `E[sqSum (polyDerivs L)] ≤ m E[sqSum L]`;
* `towerEnergy_eq_zero_of_lt`: derivatives of order greater than `m` of a polynomial of degree
  at most `m` vanish.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace RegularityStructures

variable {n : ℕ}

                                                   
                                                                         
                            

                                                                             
                                                                                     
                                                              

                                                               
                                                                               
            
                                        

                                                               
                                                                                
                        

end RegularityStructures

end

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

                                                                                             

                                                                                             
                                                       

                                                            
                                                         

                                                                        
                                                              
                  
               
                            

                                                                               
                              
                 
                                      
                                            
                     

                                                                                           
                   

                                                                                          
                                                                                           
                   

                                                            
                                                                                 
                                 
                       
     

                                                              
                                                                         
                  
               
                                                                                      

                                                                                     
                                                                                              
                                              
      

                                                        
                                                                                           
                                 
                                                                   
                  
               
                  
                                                     
        

                                                                          
                                                    
                  
               
                  
                                                    
                                                            
       

                                                                                   
                                                                                           
                  
               
                  
                                                                          
        

                                                                                             
                                                                                    
                                          
                                                                
                                                                                     
                                                                                             
                                                 
                                                                     
                                                                                            
                                                      
                                                                           
                                                                                  
                                                                                   
                                                                           
                                                                                 
              
                                                      
                                                                        
                      
                                                                   
                                                                                           
                                                   
                                                                         
                                            

                                                                                         
                                                         
                                     

                                                   
                                                                                         
                                                                          
                  
                                                    
            
                                                                    
                      
                                                  
                                                  
                              
                                              
           
                          
                             
                                                                

                                                                             
                                                                                             
                        
                                                          

                                                                           
                                            
                  
               
                  
                                                                     
        

                                                          
                                                                      
                                                                          
                                                                                

                                                                                       
                                              
                                                                       
                                                              
                                    
                    
                                                 
                                                                             
                                               
                                                                                       
                                        
                
                      

                                                                                               
                                                                        
                                              
               
                                           
                                                                    
                                                        
                                                                               
                                                 
                                                          
                                                         

end RegularityStructures

end
