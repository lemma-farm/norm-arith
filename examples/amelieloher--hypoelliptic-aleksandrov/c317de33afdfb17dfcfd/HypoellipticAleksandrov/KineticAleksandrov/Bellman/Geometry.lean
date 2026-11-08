module

                                                                                
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Literal plane geometry for the homogeneous Bellman problem -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The anisotropic position-velocity dilation on the ambient plane. -/
def bellmanPlaneDilation (r : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (r ^ 3 * q.1, r * q.2)

/-- The polynomial whose sixth root is the source gauge. -/
def bellmanGaugePower (q : ℝ × ℝ) : ℝ := q.1 ^ 2 + q.2 ^ 6

/-- The source gauge, with homogeneous dimension four. -/
def bellmanGauge (q : ℝ × ℝ) : ℝ := bellmanGaugePower q ^ (1 / 6 : ℝ)

/-- The gauge polynomial is nonnegative. -/
theorem bellmanGaugePower_nonneg (q : ℝ × ℝ) : 0 ≤ bellmanGaugePower q := by
  exact add_nonneg (sq_nonneg q.1) (Even.pow_nonneg (by decide : Even 6) q.2)

                                                             
                                                   
                                              
             
           
                                     
                                        
                                                                                       
                               
                                       
                            
             
                                                                      
                                                         
              
                                

                                                   
                                                        
                                                                                    
                                                 
      

                                                                
                                                                
                                                                      
                                               
                                                                    
                                          
                                                                             
            
        
     

                                                       
                                                                     
                                                               
         
          
                                                  
                                              
                                                                          
                                             

                                                               
                                                                              
                                                                      

                                                  
                                                         
                                                                                            
                                                          

end HypoellipticAleksandrov.KineticAleksandrov
