module

public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.Distributions.Beta

public section

/-!
# Transition-point algebra and scalar exclusion

These are the algebraic conclusions used in the revised manuscript's Section 8
and the parameter estimates in Section 16. They do not assert existence or
convergence of a CK solution. In particular, `zero_plateau_excluded` takes the
strict scalar sign property as a named analytic hypothesis; obtaining this
property from the CK equations belongs to Section 6.
-/

namespace SphericalAging.CriticalEndpoint

noncomputable section

                                            
                                                                           

                                                       
                                            
                                                               

                                                                          
                                                         
                                               

                                                 
                                                  
                                                         

                                                       
                                                     
                                                               

                                                     
                                                        
                                               

                                                                      
@[expose] def relaxationParameter (p : ℕ) (q : ℝ) : ℝ :=
  ((p : ℝ) - 2) * (1 - q) / (2 * q)

                                                   
                                
                         
                                                
                                           

                                                      
                                
                         
                                                
                                                            
          

                                                  
                               
                        
                                                
                                       
                                                 
                                                 
            

                                                       
                                                    
                         
                                                
                                            
            
      

                                                                   
                                                    
                                 
                                                                       
                                                
                                      
                                          
                                          
                                             
                                    
                                         
                              
            

                                                                                 
                                                    
                                                                    
                    
                                         
                                             
                                                
                                            
      
                                                 
                                                                     
                                                                   
                                   
                                                             
                                            

                                                                 
                                                                  
                                                                                  
                         
                                             
                     
      

                                                                                
                                                                   
                                                 
                                                            
                                         
                                                                   
                                                           
                                                            
                           
        
                                                   
                                                         
                                          
                                                                             
                                 
                                            

                                                                             
                                      
                                                      
                                                                           
                                        
                                           
           

                                                                           
                                                                        
                                                                  
                                          
                                                         
                                      
                                          
                                                             
                                                
                                       
                                                        
                                               
                                               
                                         
                                     
                                
           

                                                                           
                                                                           
                                                          
                                
                                                                          
               
                                              
                                                              
                                                                 
          

                                                                       
                                                                         
                                                                          
                                                                        
                                                             
                                                     
                                                   
                                                        
                                                
                                                       
                                                    
                                     
                                                                                  
                                       
                                            
            
                                      
                                                    
                                           
                              
                           
                           
              
                         
              
                                           
            
                                                            

                                                                           
                                                                           
                                                                
                                                                 
                                                        
                                                                  
                                                   
                                          
                                                                             
                                                              
              
                                                   
                                   
                       
                                               
            
                                       
                 
                                                                         
                                                                      
                     

                                                                 
                                                                   
                                                     
                                                
                                            
                                         
                                                                   
                           
              
                                      
                                                             
                                                                   
                       
           
      
                                                           
                                                                              
                                             
                                                                        
                              

                                                                              
                                                                  
                                                                   
                                 
                                                     
                                                
                                       
                                            
                                             
                                                 
                                                
                                                                  
      
                                                       
                                                     
                                                                       

                                                                          
                                               
                                                                      
                                                                   
                                                         
                                
                                                
                                       
                            
                                     
                                         
                                           
                                                
      
                                                         
                                                               
                                
                  
            
                                                   
                                                                                     
                                                                         

                                                                        
                                   
                                                              
                                                                  
                                           
                                          
                                                      
                                             
                                            
                                                             
                                                                   
                                         
                                           
                                                                                        
        
                                                                  
                                    
                                                           
                                                                                        
                                                  
                                                                             
                                         
                                                         
                                                                  
                                    
                            
                    
        
                    
                                         
          

                                                                             
                                                            
                                                                  
                            
                                                
                                                 
                                            
            

                                                                  
                                                                
                                                                          
                                                                   
                                                
                                                  
                                                     
                                  
                            
                                                         
           

                                                                                
                                                                    
                                                                                 
                                                
                                            
                                             
             
           
                                                             
                             
             
           
                                                      
                                    
             

                                                                               
                                                                
                                                                          
                                                             
                                                               
                              
           
                                                                
          

                                                                              
                                                                 
                             

                                                               
                            

                                                                         
                        

                                                                                        
                                

                                                           
@[expose] noncomputable def exponentCoefficient (a : ℝ) : ℝ :=
  Real.Gamma (1 - a) ^ 2 / Real.Gamma (1 - 2 * a)

/-- The coefficient is positive throughout the physical exponent interval. -/
theorem exponentCoefficient_pos (a : ℝ) (ha : a < 1 / 2) :
    0 < exponentCoefficient a := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - 2 * a := by linarith
  unfold exponentCoefficient
  exact div_pos (pow_pos (Real.Gamma_pos_of_pos h1) _) (Real.Gamma_pos_of_pos h2)

                                                                  
                                                

                                                                    
                                                                 
                                                                     
theorem beta_gamma_balance (a : ℝ) (ha : a < 1 / 2) :
    (1 - 2 * a) * ProbabilityTheory.beta (1 - a) (1 - a) =
      exponentCoefficient a := by
  have hρ : 0 < 1 - 2 * a := by linarith
  have hρn : 1 - 2 * a ≠ 0 := ne_of_gt hρ
  have hΓn : Real.Gamma (1 - 2 * a) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hρ)
  have hrec : Real.Gamma ((1 - a) + (1 - a)) =
      (1 - 2 * a) * Real.Gamma (1 - 2 * a) := by
    have hadd : (1 - a) + (1 - a) = (1 - 2 * a) + 1 := by ring
    rw [hadd]
    exact Real.Gamma_add_one hρn
  unfold ProbabilityTheory.beta exponentCoefficient
  rw [hrec]
  field_simp

end

end SphericalAging.CriticalEndpoint
