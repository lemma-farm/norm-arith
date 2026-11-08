module

public import AmbidextrousSofa.Analysis.ExactEstimates

@[expose] public section

/-!
# The height where the two initial energy tests balance

The dry endpoint bounds momentum between `b` and `b + 1/4`. At radius
`√(5-b²)`, the upper floor test meets four at one height in the canonical
interval. Squaring that positive comparison gives a decreasing polynomial.
Newton brackets start from the already proved canonical height interval.
-/

noncomputable section

open Set

namespace AmbidextrousSofa.Analysis

abbrev tiltedBalanceMomentum (h : ℝ) : ℝ := -1 / 2 + 5 * h / 4

abbrev tiltedBalanceFloorOffset (h : ℝ) : ℝ :=
  (5 - tiltedBalanceMomentum h ^ 2) + (tiltedBalanceMomentum h + 1 / 4) ^ 2 +
    (tiltedBalanceMomentum h + 1 / 4) * (1 - h) - 4

abbrev tiltedBalanceGap (h : ℝ) : ℝ :=
  tiltedBalanceFloorOffset h ^ 2 - (5 - tiltedBalanceMomentum h ^ 2) * h * (2 - h)

abbrev tiltedBalanceDerivative (h : ℝ) : ℝ := (-455 + 686 * h - 180 * h ^ 2) / 64

                                              
                                                                    

                                              
                                                                                   
                                                                                          
      

                                                                                         
                     
                                             
                            
                                                                               
                                                        
                                
                   

                                                                                       
                                                                                
                                                                                          
                                               
                                                                                      
                                                                    
                    

                                                                     

                                                                              
                                                 

                                                                             
                                                 

                                                               
                                        
                                                                                
                                                                                            

                                                                              
                                       
                                
                                    

                                                           
                                                       
                                                           
                                                  
                                                  
                                                                                   
                                    
                                                                                   

abbrev tiltedBalanceLowerStep (l : ℝ) : ℝ := l - tiltedBalanceGap l / tiltedBalanceDerivative l
abbrev tiltedBalanceUpperStep (l u : ℝ) : ℝ := u - tiltedBalanceGap u / tiltedBalanceDerivative l

                                            
                                                                                                   
                                                    
                                                            
                                                                 
                                                                               
                                   
                                                                
                                   
                                                      
                                                      
                                                   
             
                                 
                                                                                         
                                    
                
                                                                
                      
                                 
                                                                                         
                                    
                
                                                                
                      

                                                                
abbrev tiltedBalanceLower₁ : ℝ := tiltedBalanceLowerStep 0
abbrev tiltedBalanceUpper₁ : ℝ := tiltedBalanceUpperStep 0 (1 / 3)
abbrev tiltedBalanceLower₂ : ℝ := tiltedBalanceLowerStep tiltedBalanceLower₁
abbrev tiltedBalanceUpper₂ : ℝ := tiltedBalanceUpperStep tiltedBalanceLower₁ tiltedBalanceUpper₁
abbrev tiltedBalanceLower : ℝ := tiltedBalanceLowerStep tiltedBalanceLower₂
abbrev tiltedBalanceUpper : ℝ := tiltedBalanceUpperStep tiltedBalanceLower₂ tiltedBalanceUpper₂

                                                                               
                                                  
                                                                               
                                           
                                       
                                                                                
                                                                                          
                                                                                
                                                                                
                                  
                                                                                   
                                                                                                  
             
                                                                                
                                                                       
                                                                                

                                                                             
                                                                                         
                                            
                            
                                                                                  
                                                                                         
                           
                       
                       
                                                                                 
                      
                      

                                       
                                                         
                                                               
                                                                                       
                                                                     
                                                                             
                                    
                                                                  
                                             
                                                                       
                                
                                               
                                                                      
                                                                  
                                                         
                                         
                                                                           
                                                                             
                                                                        
                                                                                                                 
                                                  
        
                                     
                                
                                                                              
                                                                   
                                                        
                                                                                                                   
                                                                           
            
                                 
      

end AmbidextrousSofa.Analysis
