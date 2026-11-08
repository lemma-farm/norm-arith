module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeakDerivatives.CutoffZeroExtension
public import DedekindZetaZeroFree.Analysis.Sobolev.Approximation.CompactInteriorH1Density

@[expose] public section

noncomputable section

set_option maxHeartbeats 1500000

namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

open MeasureTheory KPContLocalNorm
open scoped Convolution

                                                                                          
                                                         
                                                                             
                                                                
                                                                                          
                                   
                                                                                          
                                   
                        
                        
                                                                             
           
                                                          
              
            
                
                                                                       
                                                                       
                                        
                                         
                                           

theorem norm_averaged_translateL2_le {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Space n))) (φ : ContDiffBump (0 : Space n)) :
    ‖∫ t, φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f t‖ ≤ ‖f‖ := by
  calc
    _ ≤ ∫ t, ‖φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f t‖ := norm_integral_le_integral_norm _
    _ = ∫ t, φ.normed volume t * ‖f‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t), KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2_norm]
    _ = ‖f‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem convolution_integral_norm_sq_le {n : ℕ}
    (g : Space n → ℂ) (hg : MemLp g 2 volume) (hg1 : Integrable g volume)
    (φ : ContDiffBump (0 : Space n)) :
    (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ^ 2) ≤
      ‖hg.toLp g‖ ^ 2 := by
  let a : Lp ℂ 2 (volume : Measure (Space n)) :=
    ∫ t, φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 (hg.toLp g) t
  have hae := KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.averaged_translateL2_ae g hg hg1 φ
  have heq : (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ^ 2) = ‖a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [heq]
  exact pow_le_pow_left₀ (norm_nonneg a) (norm_averaged_translateL2_le _ φ) 2

                                                                          
                                                    
                                                            
                  
                   
                  
                                                                                

                                                                                  
                                                  
                                                          
                  
                   
                  
                                                  
                                                                          

                                                                        
                                                  
                                                
                                                                        
                              
                                                      
                                     
                                                         
                                 
              
                  
                                   
                                                     
                                                             
                                                                                                   
                                       
                                                                                          
                                                                                                 
                                                                        
                                          
                        
                                                        
                                                                              
                                                                   
                                                   
                                                                              
                                                           
                                                  
                                        
                                                     
                                                                    
                                 
                                          
                  
                                                     
                                                                                       
                                                        
                                                                
                                                                                    
                                                                       
                                       
              
                                                              
                                                                
              
                                                                   

                                                                             
                                        
                                                                                         
                                                                                                 

                                                              
                                                 
                                                           
                                        
                          
                                               
                                                                                
                                               
                                             
                                                                    
                                                                
                                                             
                                                                              
                                    
                                                      
                
                                           
                                                           
                                            
                                                      
                                
                                                                     
                                           
                                                                
                                                   
                                               
                                                                                          

                                                                                       
                                                                           
                                      

                                                                         
                                                    
                                             
                                                                                     
                                                                                    
                                    
                                                            
                                                            
             

                                                          
                                                                
                                
                                                              
                                            

                                                                      
                                     
                                                               
                                                                                          
                                                         
                                                                                  
                                                                         
                                                  
                                                                                                  
                              
              
                                                        
                                
                                 
                                                              
                                                                    
                                               
                                                                                             

                                                                                         
                                                                     
                                                          
       
                                                                                                                 

                                                                                      
                                                                             
                          
                          
                                                 
                                                                              
                                                 
                                           
       
                                                                                 
                                        
                                                                                                 
                                                    

                                                                                        
                                                                                 
                                                              
                               
                                     

                                                                                       
                                                                                 
                                          
                                           
                             
                                                                                       
                                                                                                              

                                                                                
                                                  
         
                                    

                                                       
                                    
                                             
                                                                                 
                                                                                        
                                       
                                           
                                                         
                                                                                            
                                                                                                                 
                                                                     

                                             
                                                  
                                                

                                                              
                                                    
                                                           
                                         
                                                     
                                            
                                         
                                      
                                              
                                            
                  
                                
                                     
                                                             
                                                         
                                                                     
                                              
                                                        
                                                                             
                                                                                 
                     
                                                              
                                                                                              
                             
                        
                
                                
                                               
                                                                                           
                              
                                                  
                                                            
                                                            
                                                                                     
           
                                                      
                                                    
           
                                                                                    
                                                                 
                                                              
                                                                            
                                                                 
                                                        
                             
                             
                
                                                                                              
                                                                             
                                                          
                                        

end DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior

end
