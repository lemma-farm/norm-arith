module

public import RoughRegime.ProjectionPolynomial
public import RoughRegime.CombinedAnalytic
public import RoughRegime.ProjectionFrame
public import Mathlib

@[expose] public section
/-! Concrete source Gram-residual polynomial approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial RealInnerProductSpace
namespace RoughRegime.ProjectionApproximation
open RoughRegime.ProjectionPolynomial RoughRegime.CombinedPolynomial
open RoughRegime.CombinedAnalytic RoughRegime.ProjectionGram
open RoughRegime.HilbertGram RoughRegime.ProjectionFrame

                                                           
                                    
                                                                   
         
                                         

                                                           
                                                                                    
                                                    
                                                               
                                           
                                                           
                        

                                                               
                                                                                    
                                                        
                                                              
                                              
                                                                                   
                                              
                                                                      
                                                                 
                                                                  
                                                                     
                                
                                                       
                                                                
                                  
                                                                                          

                                                                     
                                                                                  
                                    
                                                                       
                                                                 
                                                  
          
                                                                            
     

                                                                     
                                                   
                                                                                 
                                       
                             
                                    

                                                                       
                                                               
                                                                                         
                                                           
                                                                     
                                                  

                                                                               
                                                              
                                                                                  
                                                               
                                                                               
                                         
                                                       
                                                                             
           
                                                 
                                                         
         
              
                                
                                             

                                                                      
                                                                                
                                                                           
                                                                                         
                                                                        
                                                          
                                                          
         
                                                                        
                              
                                                                          
         
        
         
                                                                                      
         
          
                 

def bilinearPolynomial {σ : Type*} {n : ℕ}
    (u : Fin n → MvPolynomial σ ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (v : Fin n → MvPolynomial σ ℝ) : MvPolynomial σ ℝ := u ⬝ᵥ S.mulVec v

                                                   
                                                                                  
                                              
                                                                           
                                       
                                                            
                           
                 
                                             
           
                                                
                                                    
                                  
                                               
             
                                                                                   
                                                                      

                                                             
                                                                                  
                                    
                                                    
                                             
                                                                                       
                                                 
         
          
                                              

end RoughRegime.ProjectionApproximation
