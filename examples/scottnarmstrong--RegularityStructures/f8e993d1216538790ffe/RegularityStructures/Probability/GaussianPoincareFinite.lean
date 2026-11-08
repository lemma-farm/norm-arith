/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.FiniteTensorization
public import RegularityStructures.Probability.GaussianPoincareClosure
public import RegularityStructures.Probability.GaussianPolynomial

/-!
# Finite-dimensional Gaussian Poincare: slice infrastructure

The product proof uses the first-coordinate decomposition of a finite product Gaussian.  The
lemmas below make the corresponding `Fin.cons` derivative and polynomial-growth calculations
explicit.  The resulting induction is the finite-dimensional form used for the covariance and
white-noise estimates (Hairer--Steele, Definition 2.20 and Remark 2.22).
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

                                                                
                                            

                                                        
                                   
                                                                 
                  
             
                                             
                                                                              
                       
              
                      
             
                               
                                                  
                                                                     
                               
                                                
                                                                           
                          
              
                                               
                                                                 
                            
                       
                   

                                                                   
                                          
                                                                         
                                                              
                                                     
                                         
                                                                               
                       
           
                       
             
                                                                  
                                                                       
                               
                                     
               
                                               
              
                                                         
                
                      
               
                                      
                                                               
               
            
                                                              
                                                                  
                                 
                                 
                                                                           
                                                  
                                                                               
                                     
               
                                                   
              
                                                                             
                
                     
               
                                 
                                                           
                                       
                                                                      
                                                                     
                                 
           
                
           
                                           
                 
           

                                                                
                                                      
                                                 
                                                    
                                                                             
                                       
                     
                                                                                              

                                                                          
                                
                                     
                                                  
                             
                                                 
                                                               
         
                                                            
                                      
                                           
                                      
             
                                       
                                       
                                                
      
                                                                
                                          
                                       
                                               
                  
             
                           
          

                                                                        
                                
                                     
                                          
                                     
                                                 
                                                               
         
                                                            
                                      
                                           
                                      
             
                                       
                                       
                                                
      
                                                                
                                          
                                       
                                               
                  
          

end RegularityStructures

end
