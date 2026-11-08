module

public import RequestProject.Euler.AnalyticContourCompositionBounds
public import RequestProject.Euler.ContourCrossLogLittle

/-! Genuine preservation of the original little contour space by
composition with an analytic physical field. Smooth target contours
approximate the actual target in the original Banach norm. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff BoundedContinuousFunction

namespace Euler2D

theorem exists_contour_value_ball_neighborhood {γ : ℝ≥0} (Z : ContourC1Space γ)
    {U : Set ℂ} (hU : IsOpen U) (hZ : ∀ x, ContourC1Space.toBCF γ Z x ∈ U) :
    ∃ r > 0, ∀ x, Metric.ball (ContourC1Space.toBCF γ Z x) r ⊆ U := by
  have hc : IsCompact (range (ContourC1Space.toBCF γ Z)) :=
    isCompact_range (ContourC1Space.toBCF γ Z).continuous
  obtain ⟨r, hr, hsub⟩ := hc.exists_thickening_subset_open hU (by rintro y ⟨x, rfl⟩; exact hZ x)
  refine ⟨r, hr, ?_⟩
  intro x y hy
  apply hsub
  exact mem_thickening_iff.mpr ⟨ContourC1Space.toBCF γ Z x, mem_range_self x, mem_ball.mp hy⟩

                                             
                                                         
                                                                         
                                                  
                                                               
                                    
                                            
                                                      
                                                                           
                                                           
                                                                             
                                                                                            
                           
                                                                                          
                                                                                
                                                          
                               
                                                                      
                                            
                                                                                                       
                                                                                    
                                                 
                                                                                      
                      
                                                  
                                                       
                                          
                                                   
                                                    
                  
            
                                                              
                                          
                                                                                     
                                                                                 
                                                                  
                                                                                       
                                                  
        
                                                 
                                       
                                                                                     
                                                              
                                                                      
                                                                             
                                                                                             
                                           
                                               
                                                          
                                                    
                                                            
                            
         
                                                            
                                                                        
                                     
           
                                                                     
                                                   
                                                           
                                                         

                                    
                                                         
                                                                         
                                                  
                                                               
                                    
                                            
                                                                              
                                                                         
                                                                              

                                                     
                                                         
                                                                         
                                                  
                                                               
                                    
                                            
                                                      
                                                                                                      
                                            

end Euler2D

end
