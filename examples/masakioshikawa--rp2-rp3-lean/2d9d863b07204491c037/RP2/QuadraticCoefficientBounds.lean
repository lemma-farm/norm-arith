module

public import RP2.QuadraticMixedJets

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

theorem mixedAB_norm_le : ‖mixedAB‖ ≤ 1 := by
  have he : mixedAB = (1/2 : ℝ) • (axisA*axisB+axisB*axisA) := by
    have h := congrArg matrixOperator mixedMatrixAB_sym
    simpa only [map_smul, map_add, map_mul, mixedAB, axisA, axisB] using h
  rw [he, norm_smul]
  have hab := (norm_mul_le axisA axisB).trans
    (mul_le_mul axisA_norm_le axisB_norm_le (norm_nonneg _) zero_le_one)
  have hba := (norm_mul_le axisB axisA).trans
    (mul_le_mul axisB_norm_le axisA_norm_le (norm_nonneg _) zero_le_one)
  have hsum := norm_add_le (axisA*axisB) (axisB*axisA)
  norm_num at hab hba ⊢
  linarith

                                               
                                               
                                                         
                    
          
                          

                                               
                                               
                                                         
                    
          
                          

                                                 
                                                            
                                                                                    
                    
                                              
                                                   
                                                   
          
          


namespace SpinSystem
                                              

                               
                                                                       
                                               
                               
                                        

                               
                                                                    
                                                          
                                
                                                    
                                      
                                                
                                                            
                                    
                                                                
                           
                
                                                             
                                
                                                     
                                                    
                                                    
                                        
                                         
                                                        
                
                                                                                                                  
                                                         
                                                                                                                      
                                                        
                
                                                                                                                  
                                                                  
                               
                                                                 
                           
                                                                
                                 
                                                                
                                            
                                                               
                                                                
                                                                                                                                                      
                                                                
                                 
                                                                
                                            
                                                               
                                                                
                                                                                                                                                      
                                                               
                                                                                        
                                            
                                                                                                
                                                             
                                                                                     
                      
                                                           
                                                                                        
                                          
                                                             
                                                                                          
                                                              
                                                                 
                                                                                          
                                                                                  
                                                                                                                                                                                                             
                                                                        
                                                             
                                                
                                                                                                   
                           
              
                                                                                                                               
                                                                                                                                
                                              
                                              
                                              
                                                
                                                
                            

end SpinSystem
end
end RP2.Quadratic
