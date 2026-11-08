module

public import SKConstants.GibbsVariational
public import SKConstants.EuclideanMatrix
public import Mathlib
public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace SKConstants

                                                      
                                    
                                                                                
                                                                               
                       
                     
                         
           
                     
                           
                                                                             
                      
                
                                                                 
                                                             
                                         
          

                                                     
                                    
                                                                                
                                                                           
                      
                                                            
                                                  
                                                                        
                           
                                                                                      
           
                                             
                                                            
                                                   
                                                                        
                           
                                             

                                                       
                                    
                                                                              
                  
                                                                        
                          
                                                      
                                                                                    
                                                                                      
                                                                            
                                                                    
                                                                                        
               
      
                                                                        
                                                                                
                 
                                     
                  
                                                                                
                                                     
                    

                                                        
                                    
                                                                              
                  
                                                                                           
                                                                                   
                                             
                                                                          
                                                           

                                                
                                    
                                                                                
                                                                                       
                 
      
                                                               
                             
               
                                                            
                                                                                             
                                                                    

@[expose] def spinEuclidean {n : ℕ} (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (signedSpin x)

                                                                                    
                                     
                                     

theorem quadraticHamiltonian_eq_inner {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    quadraticHamiltonian W x = (1 / 2) * inner (𝕜 := ℝ) (spinEuclidean x)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W (spinEuclidean x)) := by
  rw [Matrix.inner_toEuclideanCLM]
  change (1 / 2 : ℝ) * (∑ i, ∑ j, signedSpin x i * W i j * signedSpin x j) =
    (1 / 2 : ℝ) * (∑ i, signedSpin x i * (∑ j, W i j * signedSpin x j))
  congr 1
  simp_rw [Finset.mul_sum, mul_assoc]

                                                 
                                                 
                                                        
                                                                                            
                                                         
                                                                     
                                                                                         
                                             
                                                                        
                                                                                
        
                                                
                                            
               
          

end SKConstants
