-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.ODE.Linear.Basic
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Volterra operator for bounded measurable linear coefficients

The interval path is represented by a `ContinuousMap` on `Icc a b`.  A continuous clamping
extension lets us state Bochner integrability on the ambient real line without adding arbitrary
measurability assumptions outside the interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace AVenhance.Infra.ODE

                                                                             
                                                           
                                                                             

variable {E : Type*} [NormedAddCommGroup E]

                                                                                                  
                                                                      
                                   

                                                                            
                                        
                         
                                                                      
                                                                  

       
                                                                         
                                                                      
                                                                      

variable [NormedSpace ℝ E]

/-- Data for a bounded measurable linear equation with an L¹ forcing on `[a,b]`. -/
structure LinearODEData (a b : ℝ) (hab : a ≤ b) where
  A : ℝ → E →L[ℝ] E
  f : ℝ → E
  y₀ : E
  operatorBound : ℝ
  operatorBound_nonneg : 0 ≤ operatorBound
  operator_aestronglyMeasurable : AEStronglyMeasurable A volume
  operator_norm_le : ∀ t, ‖A t‖ ≤ operatorBound
  forcing_intervalIntegrable : IntervalIntegrable f volume a b

namespace LinearODEData

variable {a b : ℝ}
variable {hab : a ≤ b}

                                                             
                                                                               
                                     

                                                                   
                                                                       
                                  
                            
                                                            
                                                                        
                                                                         
                                                                      
                                                                     
                                                                             
                                                              
                                     
                                                          
                   
                                                                                                 
                   
                                                                          
                                                                           
                               
                         
                              
                                                                 
        
                                                                
                                    
                                               
                                                                
                                                
                                                                              
                                                                      
                                                 
                                                                   

                                                            
                                                                 
                                             
                                                   
                                                                             
                                                                 
                                                                                       
                                                                                     
                                   
                                                                       
                                                            

       
                                                           
                                       
                                                               

                                                                                
                                                        
                                                                      
                   
                                                            
                                                                              
                                 
           
                                                                      
                
                                                                     
                                                     
                                
                                       
             
                                                                                                  
                                       
                                            
                                        
                               
                      
                                                  
             
                                                                                                  
                                       
                                            
                                        
                               
                      
                                                   
          
                           
                                                                            
                            
                                                                                        
                                                        
                                                         
                                                        
                                                                       
                                        
                                              
                                                      
                                      
                                                        
                      
                                                                           
                                                                                               
                           
                                                  
                                                         
                
                    
              
                                                                                         
                                                                
                                                         
                               
                                       
                                      
                                                                                      
                                                                             
                                 
                                                                                    
                                                               
                                                     
                                                                                    
                                         
                                                                        
                                                                                          
                           
                     
                                                         
                                                    
                        
                                    
                                                                                      
                                                           
                                                      
                                     
                                                                                       
                                                                                                     
                      
                  
                                                                    
                                   
                     
                      
                        
                
                      

                                                                                                 
                                                  
                                                                        
                                                    
                                                                        
                                               
                                                          
                                                                                  
                                                                                      
                                                                                   
         
                                          
                                                    
                                         
      
                                                            
                                                                             
                                              
                                                                          
                                                        
                                                        
                                                                                
                                                              
                                             
                                      
                                                                       

                                                                           
                                                             
                                          
                                                                     
                                    
                                                                           
                   
                                                                
                                         
                                                            
                             
                                      
            
                                                    
           
                                                         
                                        
                                                  

                                                                                     
                     
                                                                                 
                  

                                                                               
                                               
                                          
                                              
                                                                   
                                               
                                                                      
                    
            
                               
                                                                  
                                    
           
                    
                              
                  
                  
                                                      
                                                                               

                                                                                  
                                   
                                                            
                           
                                                                       
            
                            
                                                         
      
                                                               
                                   
                           
                                                     
                                              

                                                                                                 
                                       
                                                              
                    
                                                                         
             
                                         
            
                           
           
                              
                                                     
                                                          
                       
                 

                                                                                            
                                                 
                                                            
                           
                                                                
                                    
                                 
                                                              
                                                  
                                    
                                                     

                                                                                               
                                                                            
                                          
                         
                                                                     
                                                                    
                                                  
                                                                              
            
             
                                                    

                                                                                    
                                
                     
                                                            
                           
                               
                                    
                                                     
                                    
                                 
                                                              
                                                  
                                    
                                                      

end LinearODEData

end AVenhance.Infra.ODE
