module

public import HypoellipticAleksandrov.Parabolic.HarnackABP
public import HypoellipticAleksandrov.Parabolic.EllipticityClosure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Local geometry for the near-one density argument

This file records the coordinate containments and boundary-closure facts for
the fixed local ABP cylinder used in the near-one density-to-point argument.
It contains no PDE estimate or barrier operator calculation.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

                                                                            
                                  
                                                             
                                           
                                                                
              
                                              
                                                   
                                                     
                                    

                                                                        
                      
                                                                         
            
                                               
                                       
                  
                                      
                                                
                                                           
                                                                        
                                          
                                                                   
                                                 
                                     
                          
                                                
                                                   
                                
                  
                   
                           
             
                                
                  
                          
                                                        
                                                                              
        
                                      
                                                            
                                          
                                             
                                                             
                                               
      
                                                           
                                                
                   
                                      
                                                             
                       
               

                                                                            
             
                                               
                                                         
            
                                                                                  
                                                    
                                                   
                                                      
                                                  

                                                                             
             
                                                
                                                         
            
                                                                    
                                                                        
                                 
                                             
                                       
                                            
                                             
                         
                                                          
                                                                     
                    

                                                                   
                                                            
                                                             
                                                                    
                                                         
                       
                                                                   
                                      
             
             
             
             
           
                                                     
                                                                       
                         
                                                                                            
                                     
                                                        
                            
        
                                                        
                                                 
                                                          
                                              
                                                                   
                                              
                          

                                                                             
                                           
theorem localABPInterior_subset_parabolicBox_one {d : ℕ}
    {v₀ : PDE.Vec d} (hv₀ : v₀ ∈ velocityClosedCube 0 (1 / 2 : ℝ)) :
    localABPInterior v₀ ⊆ parabolicBox 1 1 0 0 := by
  rintro z ⟨w, hw, rfl⟩
  rcases mem_parabolicInterior_iff.mp hw with ⟨hw0, hw1, hwv⟩
  apply mem_parabolicBox_iff.mpr
  constructor
  · nlinarith
  constructor
  · nlinarith
  · intro i
    have hwcoord : |w.2 i - (0 : PDE.Vec d) i| < 1 :=
      euclideanBall_subset_velocityCube (by norm_num) hwv i
    have hvcoord := hv₀ i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hwcoord hvcoord ⊢
    have hvabs : |v₀ i| ≤ 1 / 2 := by
      simpa only [Pi.zero_apply, sub_zero] using hvcoord
    rw [sub_zero] at hwcoord
    calc
      |v₀ i + (1 / 2 : ℝ) * w.2 i - (0 : PDE.Vec d) i| =
          |v₀ i + (1 / 2 : ℝ) * w.2 i| := by simp
      _ ≤ |v₀ i| + |(1 / 2 : ℝ) * w.2 i| := abs_add_le _ _
      _ = |v₀ i| + (1 / 2 : ℝ) * |w.2 i| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      _ < 1 / 2 + (1 / 2 : ℝ) * 1 := by
        have hscaled : (1 / 2 : ℝ) * |w.2 i| < (1 / 2 : ℝ) * 1 :=
          mul_lt_mul_of_pos_left hwcoord (by norm_num)
        linarith
      _ = 1 := by norm_num

                                                                             
                               
                                                               
                      
                                                                    
                                                 
      
                                                                     
                                                                             
                                                                                  
                                                                             
                                        
                                                                

                                                       
                                              
                                                
                                                                   
                                               
                                             

                                                                           
               
                                          
                                                  
                                      
                                                                          
                                                               
                                  

                                                                           
                                             
                                             
                                              
                                               
                                                            
                                           
                                       
                                           
                                                                 
                                                          
                                               
                                                      
                                   
                                                                              
                                                                           

end

end HypoellipticAleksandrov.Parabolic
