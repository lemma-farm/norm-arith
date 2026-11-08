-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianJet
public import SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.EdgeAsymptotics

@[expose] public section

/-!
# Genuine GOE spectral asymptotics

The explicit GOE matrix law of `SphericalGaussianJet` is identified with the
actual orthogonally invariant Gaussian law in the pinned OpenAI proof provider.
That provider derives tridiagonal reduction, spectral comparison and Jacobi
resolvent estimates. The asymptotic estimates below use those proofs, rather
than taking a semicircle law or spectral barrier as a premise.
-/

namespace SlowEquilibration.GOEAsymptotics

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
open OAI.CriticalSK

abbrev GaussianMatrix (k : ℕ) := OAI.CriticalSK.GaussianMatrix (Fin k)

def matrixToGaussian {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ) : GaussianMatrix k :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => W i j))

def gaussianToMatrix {k : ℕ} (W : GaussianMatrix k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => W i j

                                                                                          
                         
                                         
                          
         
                                         
                          
         
                                                            

                                                                                          
                          
         
                          
         
                                                                        
                                                                                      

                                                                                  
                                                                

                                                                                          
                                                    

                                                                       
                                                             
                                                                                      
                                                              
                                               
           
                                             
                                    
                                                                                                          
                                                                            
                                                                              
                                                                   
                                                                                                   
             
             
             
                                  
                   
          
                   
            
     

                                                                     
                                                
                                          
                                                                          
                                                            
                     
                                                                          

                                                                       
                                                                          
def eigenvalues (n : ℕ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin (n + 1) → ℝ :=
  matrixOrderedEigenvalues (matrixToGaussian W)

                                                                      
                                                                                          

                                                                                        
                                                

                                                                      
                                                        
                                                                            
                                                    
                                                                
                                                             
                                                                             
                                                                  
                                                                                            
                                          
                                                                                                                

                                                                               
                                        

                                                                                   
                                                                     

                                                                           
                                                                               
                                                                                 
                                                     
                                                                         
                                                                             
                                  
                                                    
                                                        
                                                        
                                                                              
                                                                        
                               
                                                                                          
                                      
                                                                  
                                                          
                                                                              
                               
                                             
                                                           
                                                               
                           
                          

                                                                                    
                                                                

                                                                        
                                                                            
                                                              
                                                          
                                                
                      
                                                                                   
                                    
                   
                                                  
                                              
                                       
                                        
                                                                            
                                              
                                              
                                                        
                                                                                                 
                                                                      
                
                 
                                  
                                                                              
                                                                         
                                                             
                                                                             
                                                                                              
                           
                                                                 
                                                     
                                                          
                                                            
                                                                                    
            
                                                                                
                                                  
                                                                
                                                                    
             
                                                              
                    
                                                                                         
                                                     
                                                                                             

                                                                                      
                      
                                                                               
                                    
                                                                        
                                                                                              
                 
                                                                                        
                                                                    
                                                                                      
                       
                                             
                                                                        

                                                                             
                                          

                                                                          
                                                                         
                                                                     
                                                                                   
                      
                                                                            
                                    
                                   
                                                             
                                    
                                            
                              
            
                                                                                                      
                                                                                                 
                      
                                                      
                          
                                                                                     
                      
                                              
                                               
                         
                                                                                   
                                      
                                                                                        
                                     
                                                                                             
                                                                          
                                           
          
                           
                              
            
                                           

                                                                          
                                   
                                                                              
                                                                                 
                               
                                                                              
                                                  
                                                                                              
                               
                
                                                             
                                                 
                                        
                                                                                   

                                                                          
                                                                            
                                                                                                
                         
                                                                                  
                    
                                                                      
                                                                 

                                                                           
                                                                             
                         
                                                                           
                    
                                                                      
                                                         

end
end SlowEquilibration.GOEAsymptotics
