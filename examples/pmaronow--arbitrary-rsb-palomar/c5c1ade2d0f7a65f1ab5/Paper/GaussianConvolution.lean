module

public import Paper.GaussianPositivity
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-!
# Independent Gaussian sums and heat convolution

The independent pair uses the genuine product Gaussian probability measure.
The affine sum law is proved by Gaussian convolution, including zero
coefficients. Boundedness supplies the product integrability needed for Fubini.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Paper

noncomputable def standardGaussianPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure standardGaussianPair := by
  unfold standardGaussianPair
  infer_instance

                                                 
                                                   
                                                                          
                                                                                    
                                
                                                                                    
                                
                                         
                                         
                                               
                                                        
                                             
                                                         
                                                                          
                            
                                                                   
                                                     
                                                                              
                                
                                         
                                                                       
         
                 
                                                        
                                               
         
        
        

                                                               
                                                       
                                           
                                                          
                                    

                                                                             
                                                                
                                               
                                                                 
                             
                                                                                         
                                                                                
                                                                            
                                                             
                                                     
                                                                        
                                   
                                                             
                                                  
                            
                           
          

                                                                            
                                                                          
                                                       
                                                                                         
                                                                                
                                                                   
                             
                                                                                       
                                                                            
                                                             
                                                     
                                                                        
                                   
                                                                    
                                                 
         
                            
                           
          

                                                                              
                                                             
                                                       
                                                     
                                                                   
                                                          
                                                                   
                               
                                                                     
                                        
                              

                                                                              
                                                            
                                                       
                                                  
                                                          
                                                                       
                                      

                                                                   
                                                                    
                                                       
                                                     
                                                                   
                                                        
                                                    
                                                           

                                                                     
                                                             
                                                                           
                                                                           
                      
                                                                                         
                                       

end Paper
