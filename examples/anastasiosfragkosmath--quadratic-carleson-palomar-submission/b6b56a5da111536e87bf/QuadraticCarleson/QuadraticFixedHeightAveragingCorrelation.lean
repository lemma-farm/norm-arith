/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.QuadraticFixedHeightAveragingFinite
import Mathlib
/-!
# Annular amplitude products in the fixed-height quadratic correlation

These lemmas instantiate the proved quadratic oscillatory estimate for the
actual product of two annular convolution amplitudes. Their uniform amplitude
and derivative bounds are kept explicit, to be supplied by the dyadic cutoff
lemmas rather than assumed in a headline theorem.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson

/-- Modulation of an annular amplitude by the paper's quadratic phase. -/
noncomputable def annularQuadraticKernel (a : ℝ → ℂ) (lam t : ℝ) : ℂ :=
  a t * phase (lam * t ^ 2)

                                                                                        
              
                                            
         
                                                          
           
      

                                                                      
                                                                        
                                                                         
                                                                                      
                                                                                     
                                                  
                                             
      

                                                                         
                                                                            
                                                            
                                                     
                                             
                                                                     
                                                       
                                                          
                                          
                                                           
                                                           
                                                 
                                                 
                                                               
                                                               
               
                                                
                                                  
                                                                
                                                       
                           
                                                                     
                                  
                                                                                          
                                                                                          
                                                                         
                                                                
                                                                         
                                                                         
                                                                
                                                                         
                                                                     
                                
                                                                  
                                                                                         
                                                          
                                                                                           
                                   
                                                                   
              
                                  
              
                                
                                  
              
                                
                                          
                                                     
                                             
                                       
        
                                                                
                              
                                                                  
                                    
                 
                 
                          
                                                               
                                             
        
                                                   
                                                             
                                                                       
                                                        
                                                             
                        
                                                                           
                                                                           
                                                              
                                                
                                                                                       
                         
                                                 
                                                                                          
                                                               
                                                                
                                           
                                                                             

                                                                       
                            
                                                   
                                                           
      
                                            
                          
             
                             
                              
                                                 
          
                               

                                                                           
                                                                            
                                             
                                             
                                                       
                                                       
                                                          
                                                  
                                                           
                                                           
                                                 
                                                 
                                                               
                                                               
               
                                                
                                                  
                                                                        
                                                                                         
                                                                                               
                      
                         
                                                                                     
                                                                               
                                                                    
                                                                                    
                                                               
                                         
                                                                       

                                                                           
                                                                         
                                                           
                                                             
                                                                  
                                                             
                                                       
                                                                  
                                                                            
                                                               
                                                                         
                                  
                                                                                             
                                                                      
                                                                                     
                                                                                                  
                                       
            
                                                                                            
                                                                                                         
              
                 
            
                                                   
                                                                                    
                                                               
                                                        
                                                                             
                                                               
                                                                                               
                                        

end QuadraticCarleson
