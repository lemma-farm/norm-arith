module

public import GinibrePoincare.Analysis.GinibreWeakGradient

@[expose] public section

/-! # Ordinary distributional gradients on the collision-free open set

Weighted L² values and gradients are locally Lebesgue integrable where the
Ginibre density is positive. The density-weighted weak identities imply the
usual distributional derivative identity against every smooth test compactly
supported in this open set. No reverse smooth-core approximation is assumed.
-/

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

set_option maxHeartbeats 300000

                                                                                
                                                                                           
                                         
           
                                                                            
                                                  
                                
                                                                                   
                        

                                                                                           
                                                     
                                                                  
         
                                    
         
                                                                                    

                                                                                     
                                                                 
                                                     
                                                      
                                                                        
                                         
                                                
                                                          
                                                                                              
         
          
                                                                            

                                                                                             
                                                           
                               
                                     
                                                                      
                                            
                                                                                       
                                                                  
                                
                                                                                  
                                                   
                                                                                     

                                                                                            
                                                                          
                                                                   
                                                                              
                                               
                                                                         
                                                                          
                                                                      
                                                
                                                                        
                                                                             
                                                      
                                                                
                                              
                
                                                                        
            
       
                                                                        

                                                                               
                                                                   
                                                                       
                                                   
                                               
                                                                          
                                   
         
                                                  
                                  
              
                                                                               
                                                                   
                                                                 
                                 
             
                                                                                      
                        

                                                                
                                                          
                                                                               
               
                  
          
              

                                                                                        
def IsGinibreDistributionalGradient (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) : Prop :=
  LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume ∧
    (∀ k : Fin n × Fin 2,
      LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume) ∧
    ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
        (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k))

                                                                                                      
                                                                 
                                   
                                                                    
                                                                                    
                                                                                  
           
                                                       
                                                
                                                                           
                                                                              
                      
                                         
                                                         
                                                                                     
                                                                                           
                                                 
              
                           
                                      
                  
                                                                                   
                                                      
                 
                       
                                   
                                                               
                                                                       
                                                           
                
                                                                                                    
                
                                                                         
                                                                                     
                                                           
                                                                  
          
                                                                                 
                                         
                                                                           
                                                                           
                      
                                                                             
              
                               
          
                                                                  
                                     
                  

                                                                                       
                                                                         
                                    
                                                                 
                                                                                    
                                                   
                                                  

                                                                              
                                                 
                               
                                                                               
                                                  
                                                                                     
                                                                                         
                                                                    
                                        
                                              
            
                                                    

                                                                                            
                                                                   
                                   
                                                                      
                                                
                                                              
                                                                          
                                              
                                                            
                                                                              
               
                                                                              
           
                                                   
           
                                             
                                                                           
                                                          
                                                                                   
                                                                                       
                           
                                                                        
                                        
                                                                        
                                        
                                                 
                                                       
                                     
                                 
                                                                       
                                                                     
                   
                                           
                                  
              
                                              
                   

end
end GinibrePoincare
