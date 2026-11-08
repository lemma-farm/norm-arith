module

public import Sidon.Analysis.FiniteFourier
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

@[expose] public section

/-! # Finite correlations and integer translations -/

noncomputable section

open scoped ComplexConjugate

namespace Sidon

                                                                        
                                                 
                            

       
                                                         
                                        
                                                       
                                                                  
                                                                      

                                               
                                                                      
                                                                   

       
                                                                   
       
      

                                                                                    
def correlation (f g : ℤ →₀ ℂ) (h : ℤ) : ℂ :=
  f.sum fun x c => c * conj (g (x + h))

                                                                
                          
                                                             
                            
              
                                   
                                                 

       
                                                                                
                    

       
                                                                                 
                                 

                                                         
                                                                             
                                                                               

                                                          
                                                                             
                                                                  

                                                         
                                                                             
                                                        

                                                          
                                                                             
                                                                  

                                                              
                                                         
                                         
                                                                 
                                                                 

theorem correlation_smul_right (c : ℂ) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation f (c • g) h = conj c * correlation f g h := by
  simp only [correlation, Finsupp.smul_apply, smul_eq_mul, map_mul, Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

                                                                   
                                                         
                                                                      
                                                    

theorem correlation_real_smul_right (c : ℝ) (f g : ℤ →₀ ℂ) (h : ℤ) :
    correlation f (c • g) h = c • correlation f g h := by
  have heq : c • g = (c : ℂ) • g := by ext x; simp [Complex.real_smul]
  rw [heq, correlation_smul_right, Complex.conj_ofReal, Complex.real_smul]

                                                                        
                          
                                                                         
                                                                                           

                                                                         
                          
                                                                         
           
                                            
                 
                        
                                                                                

                                                                   
                                                                                           
                                 
                                 
                                                                     
                                                       
                                                                       
                                
         
            
                                                    

                                              
                                                      
                                                                                      
                                                                                   
                                                                                    
                               
                            
           
      

                                                     
                                                         
      
                                                                
                                                           
                                                                              
                                         
             
                                                    

                                            
                                                                     
                                                                  

                                               
                                                                    
                            
                    

                                                      
                                    
                               
                                                            

                                                             
                                                                    
                               
                          
            
                               
                
            
                                           
                                                                           
           

                                                  
                                                     
                                                                                 
            
                
                                                      

                                                            
                                          

                                                              
                                                                 
                                                                     
                                                
                                  
                        

       
                                                                         
                                                 

       
                                                                   
                                                
       
                                 
            
                                  
                              
                          
                                    

                                                               
                                                                
                                                          
     

                                                                                 
                                                         
                                              
                                                                                
                     
                            
           
                                                      
                                                                                 
                         
                                               
      
                                                                                        
                                            
                                                                    
                                

                                                                                      
                                                                                     
                                                                      

end Sidon
