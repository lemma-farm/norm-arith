module

                                     
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! The actual unnormalized quadratic transport cost on particle configurations.
The surrounding Pi type has its usual sup norm; that norm is deliberately NOT
used as the transport cost. No transport metric theorem is assumed here. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace SharpWasserstein

abbrev Position (d : ℕ) := Fin d → ℝ
abbrev Configuration (d N : ℕ) := Fin N → Position d

def productCost {d N : ℕ} (x y : Configuration d N) : ℝ :=
  ∑ i, ∑ a, (x i a - y i a) ^ 2

                                                                
                             
                                                                             

                                                                    
                                                

                                                              
                                           
                    
                            
           
                            
           
      

                                              
                                                     
                                                                                  

                           
                                                                   
                                               

                                                                            
                                                                            
                                                                         
                                                                                 
                   

                                       
                                                                                             
                                                                       
                                                 

def HasSecondMoment {d N : ℕ} (μ : Measure (Configuration d N)) : Prop :=
  (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂μ) < ∞

                                                          
                                                        

                                               
                                                                              

                                                                        
                                                                        

                                                                      
                                                                  

                                                                
                                                     
                                                         

                                          
                                                                                           
                    
          

                                                                       
                              
                                                          
                                                               
                                      
                                                                   
                                          
                        
                                          
                        

                                                                              
                                                          
                            
      
                                                                          
                                                   
               
                                                                   
                                          
                                                                      
                                                 
          

                                                                   
                                                                                   
                                                  
                                       
                                                                                
                                                       
                
                                                       
                

                                    
                                                           
                                                                   
                                                                                         
                                         
     

                                                                          
                                               
                                                                                                 
             
                 
           
                 
            
                                                                                    
                                               

                                                                                   
                                                                                           
           
                                                                 
                                                        
                                                  
      
                                                            
                                 
                           
                                                                  
                                                               

                                                 
                                       
                                                                                   
                                            
                                                                                             
                                       
                                                      
                                                                        
                                                                
                                                            
                                                                   
                                          
                                                                             
                                                    
                                          
                                                                             
                                                    

                                                         
                                                           
                              
                                                                            
                           
                                                      
                                                                        
                                                                
                                                            
                                                                                         
                                                           
                                                                 
                      
         
                                                                    

                                                               
                                                         
                                         
                                                                         
               
         
               
          
                                                              
                                   

end SharpWasserstein
