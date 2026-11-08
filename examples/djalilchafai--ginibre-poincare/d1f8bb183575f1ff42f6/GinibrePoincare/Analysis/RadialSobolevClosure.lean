module

public import GinibrePoincare.Analysis.EntropyL2Closure
public import GinibrePoincare.Analysis.GaussianRadialLift
public import Mathlib
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

                                                                             
                                                                                      
                                       
                                                                                    
                                                         

                                                                                                  
                                                                     
                            
                                                                            
                                               

                                                                             
                                                                         
                                                                  
                     
         
                      
                                 
                                                                                                      
                                  
                                                                                                           

                                                                                 
                                                                                     
                                 
               
          
                                     
     

                                                                   
                                                     
                                                

                                                                                 
                                        
                                                                                               
                                                         
                                                        
                                                                                   
                                 

                                                                                                   
                                                                      

                                                                              
                                                       
                                                            
                                   
                                                          
                                                                                     
                                        
                                                
                                           
                                                         
                                                                      
                                                                             
                                                          
                                                                        
                                               
                       
                       

                                                                      
theorem squareEntropy_congr_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ} (h : f =ᵐ[μ] g) : squareEntropy μ f = squareEntropy μ g := by
  apply squareEntropy_eq_of_moments
  · apply integral_congr_ae
    exact h.mono (fun x hx => by dsimp; rw [hx])
  · apply integral_congr_ae
    exact h.mono (fun x hx => by dsimp; rw [hx])

                                                                        
                                                                                   
                                       
                                                 
                                        

                                                                        
                                                                             
                                                             
                                                               
                                                           
                                 
                                                                                 
                                                                              
                                                
                                
            
                              
                                                                              
                               
                                                                              
                                         
                           
                                 
                                             
             
                                                                                 
                                                      
                  
                    

end
end GinibrePoincare
