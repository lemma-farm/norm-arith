module

public import SubdiffusiveProcess.Sobolev.ResponseSpace

@[expose] public section

/-! # Positivity and linearity of the actual weak source response -/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

                                                                                
                                                                                       
                                                          
             
            
                                    
                                               
                                                                                        
                                
                                                                 
                                  
              
                        

                                           
                                                                                 
                                    
      
                           
         
                                  

                                                                     
                                                                              
                             
                                                                                        
      
                           
         
                                                       

                                                                      
                                                                               
                                   
                                                                   
      
                           
         
                                                         

                                                                    
                                                                              
                                         
                               
                                      
                                        

                                                                 
                                                                                     
                                                                   
             
           
                                                                                      
         
                                            
                                       
                 
              
                                
       

                                                                          
                                                                                 
                                                                   
                       
                                              
                                                                     

                                                                                
                                    
                                              
                                                     
                             
                                                                                 
                                          
                                 
                                 
                                                                                 
                                                                            
                                              
                                             
                                                        
                                                                                    
               
          
                                                   
                                                     
                                                           
        
                                        
                                                                 
                                                                 
                                              
                                                                    
                       
                                                         
                                                             
                                                                      
                                                
      
                                                                                    
                                                        
                                                          
                                                             
                                                                                           
                       
                     
                                          

                                                                                      
                                   
                                              
                                                                          
                                                                                          
                                                                                                
                                                                        
                                                                        
                                                                
                                                             
                                                           
                                 

                                     
                                              
                                                                        
                 
                                                                                      
                                                          
                                                                        
                                
                                    

                                                                        
                                   
                                              
                                                       
                                           
                              
                                  
                                                                          
                              
                             
                                   
                                          
                                
                             
                                                                   
                                                                   
         
                                 
                                     
                                
                                                                 
                                           
        
                                                                    
                                     
                                              
                                    
                                                   
                       
                                
                       
                                           
                           
                                                
                  
                                         
                               
                                                                       
                              
                                        
                                          
                                 
                             
          
                                                
                          
                              
                              
                                              
                                                
                                     
                                      
                         
                         
                                                                 
                                                
          
                            
                                   
                                                   
                                  
                                             
                
                               

                                                                                 
theorem sq_load_le_inverseResponse_mul_responseForm
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) (w : S.space) :
    (L w) ^ 2 ≤ inverseResponse S a L * responseForm S a w w := by
  have hquadratic : ∀ s : ℝ,
      0 ≤ responseForm S a w w * (s * s) + (-2 * L w) * s + inverseResponse S a L := by
    intro s
    have hmax := (inverseResponse_isGreatest S a L).2
      (show 2 * L (s • w) - responseForm S a (s • w) (s • w) ∈
        Set.range (fun v : S.space => 2 * L v - responseForm S a v v) from
          ⟨s • w, rfl⟩)
    simp only [map_smul, smul_apply, smul_eq_mul] at hmax
    nlinarith
  have hdisc := discrim_le_zero hquadratic
  simp only [discrim] at hdisc
  nlinarith

                                                                                     
                                           
                                              
                                                       
                                       
                       
                                                                                              
                                                              
                                         
                                                         
                                                  
                                                                          
                 
                                              
                                     
                                               
                                                                   
                    
           
       
              
                                 
           
                               

end SubdiffusiveProcess
