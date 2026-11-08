/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialCalculus
                                                                  

/-!
# Dyadic `L^p` spectral gap for Gaussian polynomials

For a polynomial `f` in `n` variables and `γ = standardGaussianMeasure n`,
`E[|f - E f|^(2^(k+1))] ≤ C^(2^(k+1)) E[|∇f|^(2^(k+1))]` with `C = 2 (2^(k+1))^2`, independent of
`n` and `f` (`integral_abs_sub_mean_pow_le`).  This is the finite-dimensional counterpart of
`whiteNoise_cylindrical_lp_spectral_gap_dyadic`: the Gaussian Poincaré inequality is applied to
powers of the centred polynomial and iterated by `lp_spectral_gap_dyadic`.  For polynomials every
integrability hypothesis of the abstract iteration holds automatically.
-/

public section

open MvPolynomial MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RegularityStructures

variable {n : ℕ}

                                                                      
                                                                          
                                           
        
                                                                                        
                                                           
                                                                                     
                                                                         
                                   
                                                          

                                                                      
                                                      
                                                          
                                                                     
                                                                           
                               
                               
          

                                                                                  
                                              

                                                                   
                                                                                                 
               
                         
                                                                                    
      

                                                                                                     
                                                                            
                                                                   
                                                           
                                                                                                  
                                                  
                                                             
                                                        
                
                              
                           
                                                                    
                                                           
                                                                      
                                                
        
              
                                                    
                    
                     
                                     
                                           
                                           
        
                                                    
                      
        

                                                                                              
                                   
                                                                           
                                                                                
                                      
                                                         
                                                                         
                                            
                                                             
                                                                 
                                                                                    
                                         
                                                                                  
                                                                          
                                    
                                             
                                                                                      
                                                         
                                                           
                                                                     
                                           
                                                                                      
                                                          
                    
                                                                                            
               
                                                                                   
                                     
                                                                                          
                                                    
                                  
                                                       
                                                                                         
                                                      
                                                                      
                                                       
                                           
          
                                                                    
                                                                              
                                                                          
                                                      
                            
                                                                                      
                              
                    
           
                                                        
                                                                                               
                                                               
                                                                 
                  
                    
                                  
                                                                  
                                                                                                       
          
                   
                                                                             
                                                  
                                   
                                                                                      

end RegularityStructures

end
