module

public import proofs.DividingCompartments.FiniteBranching


@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Actual countable-state marked laws with arbitrary probability rows.
Bounded rewards permit arbitrary immigrant laws, including infinite moments.
No recurrence or occupation conclusion is a model field. -/
namespace DividingCompartments.MarkovRenewal
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
noncomputable section

def Bounded {S : Type*} (f : S → ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C

                                                                                 
                                    
                        
                        
                                                                                         

structure Model (S : Type*) [MeasurableSpace S] where
  step : S → Measure S
  probability : ∀ x, IsProbabilityMeasure (step x)
  rate : S → ℝ
  rate_lower : ∀ x, 1 ≤ rate x

namespace Model
variable {S : Type*} [MeasurableSpace S] (M : Model S)

instance stepProbability (x : S) : IsProbabilityMeasure (M.step x) := M.probability x

theorem rate_pos (x : S) : 0 < M.rate x := lt_of_lt_of_le zero_lt_one (M.rate_lower x)

def apply (f : S → ℝ) (x : S) : ℝ := ∫ y, f y ∂M.step x

                                            
            
                                 

                                                                                 
                    

                                                             
                               
                  
                    
                                        

                                                                                       
                  
               
                
                                                                  
           

variable [Countable S] [MeasurableSingletonClass S]

theorem bounded_integrable {f : S → ℝ} (hf : Bounded f) (x : S) : Integrable f (M.step x) := by
  obtain ⟨C,_,hC⟩ := hf
  exact Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hC y)

theorem apply_bounded {f : S → ℝ} (hf : Bounded f) : Bounded (M.apply f) := by
  obtain ⟨C,hC,hf⟩ := hf
  have hi (x : S) := M.bounded_integrable ⟨C,hC,hf⟩ x
  refine ⟨C,hC,fun x => abs_le.mpr ⟨?_,?_⟩⟩
  · have hh := integral_mono (integrable_const (-C)) (hi x) (fun y => (abs_le.mp (hf y)).1)
    simpa [apply] using hh
  · have hh := integral_mono (hi x) (integrable_const C) (fun y => (abs_le.mp (hf y)).2)
    simpa [apply] using hh

                                                                                      
                  
                    
                                         

                                                                   
                                                                     
          
                                                                            

                                                                  
                                                               
                                                                         

                                                                 
                                                                         
                  
                   
                                                                                  

                                                                          
                                                                        
                  
               
                
                       
                                                                 

                                                                            
                                                          
                                                               
                  
                       
                
                                                                            
                                                                                   
                              
            

                                                                           
                                             
                                                  
                                                                       
                                           
                                                                 
           
                                                     
                                    
            
                                                                           

                                                                                      

                                                                                   
                                                                                                       
                      
                

                                         
                          
                                          

                                                           
                                                 

                                                                 
                                                                            
                                              

                                                                                                     

                                            
                                                                             

                                                                                                          

                                      
                                                                  
                                                                           
                                                                                          
                                                  
                                        
                                                               

                                                                                                  
                                                       
                                                               
                                                                                            
                                  
                                                                                  
                                       
                                                                                                       
                                                          
      

                                                  
                                                                                       
                                                                                                       
                      
      

                                                  
                                                                                                      
                                                                                                       
                      
      

                                              
                                                                       
                                                               
                                                                                             
      
                                                                                     
                                           
                                                                                                           
                                          

                                                           
                                  
                                                                                        
                                                   
                                                                                                    
                                    
           
                                                                        
                                           

                                                            
                                          
                                                                                       
                                 
           
                                               
                                                        
                                            
                                         
                                
                              
                
                                                                                        
                                                                                         
                                                
                                                     
                                                                            
             
                                             
                      
                                                         
                                                                             
                                                    
              
                                             
                                                               
                                                                   
                                                                          

                                                                               
                                                     
                                                          
                                               
                                                                                                                                 
                                                                                
                                            
                                                                                

                                                  
                                          
                                                                                           
                                                   
                                                                             
                                      
           
                                                                                           

                                                  
                                                                                             
                        
                           
                                        
                                                                                       

                                                                            
                     
                                                                                       
                                                               
                                                             
                                                                                         
                                                                                       
                                              
                                                   
                                                            
                                                         
           
                                                                         
                                                                                        
                                                                       
                                   
           
        
                    
                                                       
                                                            
                                                          
                                                              
            
                                           
                                                                                            
                                                                        
                                                                                                           

                                                    
                                                                     

                                                                                
                                                                           
                                        
                                                                     
                   
                                                                                  
                                       
                                      
                                                                                         

                                                                           
                                                                          
                                                                                
                                          
                          
                                                
                              
                                                 
                                                                
                                  
                                                                                   
                                                                      
           
                                                                          
           
                              
                                         
                       
                                                            
                                           
                                   

                                                                                 
                                                                 
                                                               
                                                                          
                                                                       
           
                     
                                
                              
           
        
                                                                            
                               
                                                                   
      
                                                                               
                                                                  
                                   
                         
                                            
                  
                                                     
            
                                                 
                                         

end Model
end
end DividingCompartments.MarkovRenewal
