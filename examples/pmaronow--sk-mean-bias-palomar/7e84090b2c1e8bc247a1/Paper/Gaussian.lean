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

noncomputable def gaussianField (β h q z : ℝ) : ℝ := β * Real.sqrt q * z + h

noncomputable def overlapMap (β h q : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (gaussianField β h q z) ^ 2)

noncomputable def atParameter (β h q : ℝ) : ℝ :=
  β ^ 2 * gaussianExpectation (fun z => sech (gaussianField β h q z) ^ 4)

                                                 
                                                                                          
                             

                                                                    
                                                          

                                            
                                                               

                                            
                                                               

                                                 
                                       

                                                   
                                              
                            

                                                  
                                                                                        
                                                                                            
                                                                                                          
                                          
                                                                             
                                                                        
                                           
                          
                                                    
                             

                                                         
                                                                       
                                               
                                                            
                                                               
                                                                        
                            
                                                                       
                                                     

                                                                   
                                              

                                                                   
                                                              
                                                                                     
                                                  

                                                  
                                                                 
                                                                                  
                                             
                                                                             
         
                                                            
                                           
         
      

                                             
                                                                                                
                                                           
                                                          
                                 
        
                                                                                            

                                                                   
                                         
                                                        
                                                                              
                                                                             
           
         
                                  
                
          

                                                                                    
                                  

                                                             
                                                 
              
                                                      
                                     
                                        
          

                                                                                    
             
                               

                                                                               
                    
                                      
                                                                                   

                                                                             
                                                                               
                                                                                              
                                                                                     
                                                                 
                    
                         

                                                                                 
                      

                                                                                        
                                                                                        

                                                                                    
                                                   
                                                                        
                                                                                         
                                                                                               
                                         
       
                                 
         
                                                            
     

                                                       
                                                                                   
                                                                      
                                                    
                                                                          
                          
                                                                             
                                                                          

                                            
                                                                                               
                                                                                              

end Paper
