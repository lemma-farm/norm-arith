module

public import RP2.QuadraticMixedJets
public import Mathlib
public section

/-! # Uniform bounds on the actual mixed RP² coefficients -/
namespace RP2.Quadratic
noncomputable section
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

theorem norm_square_le_one (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) : ‖M^2‖ ≤ 1 := by
  calc ‖M^2‖ ≤ ‖M‖ * ‖M‖ := by simpa only [pow_two] using norm_mul_le M M
       _ ≤ 1 * 1 := mul_le_mul hM hM (norm_nonneg _) zero_le_one
       _ = 1 := one_mul _

                                             
                                                                 
                                                       
                                                                          
                    
                                             
                                                                        
                                             
                                                                        
                                                      
                       
          

                                               
                                               
                                                         
                    
          
                          

                                               
                                               
                                                         
                    
          
                          

theorem mixedAABB_norm_le : ‖mixedAABB‖ ≤ 1 := by
  have he : mixedAABB = (-1/6 : ℝ) • (axisA^2+axisB^2) := by
    simp only [mixedAABB, mixedMatrixAABB, map_smul, map_add, map_pow, axisA, axisB]
  rw [he, norm_smul]
  have hsum := norm_add_le (axisA^2) (axisB^2)
  have ha := norm_square_le_one axisA axisA_norm_le
  have hb := norm_square_le_one axisB axisB_norm_le
  norm_num
  linarith


namespace SpinSystem
                                              

                               
                                                                       
                                               
                               
                                        

                               
                                                                    
                                                          
                                
                                                    
                                      
                                                
                                                            
                                    
                                                                
                           
                
                                                             
                                
                                                     
                                                    
                                                    
                                        
                                         
                                                        
                
                                                                                                                  
                                                         
                                                                                                                      
                                                        
                
                                                                                                                  
                                                                  
                               
                                                                 
                           
                                                                
                                 
                                                                
                                            
                                                               
                                                                
                                                                                                                                                      
                                                                
                                 
                                                                
                                            
                                                               
                                                                
                                                                                                                                                      
                                                               
                                                                                        
                                            
                                                                                                
                                                             
                                                                                     
                      
                                                           
                                                                                        
                                          
                                                             
                                                                                          
                                                              
                                                                 
                                                                                          
                                                                                  
                                                                                                                                                                                                             
                                                                        
                                                             
                                                
                                                                                                   
                           
              
                                                                                                                               
                                                                                                                                
                                              
                                              
                                              
                                                
                                                
                            

end SpinSystem
end
end RP2.Quadratic
