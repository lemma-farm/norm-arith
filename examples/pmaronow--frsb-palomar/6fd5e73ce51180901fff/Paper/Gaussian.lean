module

public import Paper.Hyperbolic
public import Mathlib

@[expose] public section

/-!
# Concrete Gaussian quantities

The expectations in the paper are Bochner integrals against mathlib's standard
Gaussian probability measure. We keep `q` explicit; existence and uniqueness of
the fixed point are proved separately in `FixedPointUnique.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

noncomputable def gaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1

                                                                            

                                               
                                                                      

                                                
                                                                         

                                                 
                                                                                          
                             

noncomputable def heatSemigroup (ell : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  gaussianExpectation (fun z => φ (x + Real.sqrt ell * z))

                                            
                                                               

                                            
                                                               

                                                 
                                       

                                                   
                                              
                            

                                                  
                                                                                        
                                                                                            
                                                                                                          
                                          
                                                                             
                                                                        
                                           
                          
                                                    
                             

                                                         
                                                                       
                                               
                                                            
                                                               
                                                                        
                            
                                                                       
                                                     

                                                                   
                                              

                                                                   
                                                              
                                                                                     
                                                  

                                                  
                                                                 
                                                                                  
                                             
                                                                             
         
                                                            
                                           
         
      

                                             
                                                                                                
                                                           
                                                          
                                 
        
                                                                                            

                                                                   
                                         
                                                        
                                                                              
                                                                             
           
         
                                  
                
          

                                                                                    
                                  

                                                             
                                                 
              
                                                      
                                     
                                        
          

                                                                                    
             
                               

                                                                               
                    
                                      
                                                                                   

                                                                             
                                                                               
                                                                                              
                                                                                     
                                                                 
                    
                         

                                                                                 
                      

                                                                                        
                                                                                        

                                                                                    
                                                   
                                                                        
                                                                                         
                                                                                               
                                         
       
                                 
         
                                                            
     

                                                       
                                                                                   
                                                                      
                                                    
                                                                          
                          
                                                                             
                                                                          

                                            
                                                                                               
                                                                                              

end Paper
