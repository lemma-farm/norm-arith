module

public import RequestProject.Basic

/-!
# Calculus on the torus `𝕋²`

Helper results for Lemma 1.7: Fubini on the unit cell, vanishing of the mean of a partial
derivative of a periodic function, periodic integration by parts, and the one-variable facts
(first and second derivative at a maximum) used in the maximum principle.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-- Every point of `ℝ²` is an integer translate of a point of the unit cell. -/
lemma exists_cell_rep {d : ℕ} (x : Pt d) : ∃ y ∈ cell d, ∃ n : Fin d → ℤ, x = y + intVec n := by
  refine ⟨fun i => Int.fract (x i), ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩,
    fun i => ⌊x i⌋, ?_⟩
  funext i; simp only [intVec, Pi.add_apply, Int.fract]; ring

                                                                           
                                                             

                                       
                                                                       
                                                                          
                                               
                                                                                 
                                                               
         
                                                                                                
                                                            
         
                                                                 
                                 
                                                                                           
                     
                                                  
                                 
                                                            
                         
                                                                                        
                                
                                                     
                
                             
                                                                                    
                                                                                
                                                              
                                                                                
                   

                                                    
                                                                        
                                                                          
                             
                                                         
                                  
                                                      
                                                                                            
                                                  
                                 
                                                            
                         
                                                                             
                                                       

section line
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `i`-th standard basis vector. -/
def eb (i : Fin d) : Pt d := Pi.single i 1

lemma hasDerivAt_line (h : Pt d → E) (x : Pt d) (i : Fin d) (r : ℝ)
    (hd : DifferentiableAt ℝ h (x + r • eb i)) :
    HasDerivAt (fun r => h (x + r • eb i)) (pd i h (x + r • eb i)) r := by
  have hl : HasDerivAt (fun r : ℝ => x + r • eb i) (eb i) r := by
    simpa using ((hasDerivAt_id r).smul_const (eb i)).const_add x
  exact hd.hasFDerivAt.comp_hasDerivAt r hl

                                                                                                   
                                                               

                                                                                           
                                                                 
                                                            
                                                   
                                                    
                                                                          
                                
                                                    
                                                         
                                           
                         

end line

                                                                             
                                                                                                 
                                     
                                                                    
             
                                
                                                             
             
                                                                   
                                                    
                                                                                        
                                    
                                        
               
                               
                                                             
             
                                                                   
                                                    
                                                                                        
                                    
                                        
               

section ibp
variable {d : ℕ}

                                                                       
                                               
                                                                       
           
                           
            

                                                                                       
                                                               
           
           
                                                                       
                       
                            

lemma contDiff_pd_of_C2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Pt d → E)
    (hh : ContDiff ℝ 2 h) (i : Fin d) : ContDiff ℝ 1 (pd i h) :=
  (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

                                                                               
                                                                          

                                                                                  
                                                           
                                                                        
                                                                              
                                                                                
                                                                                                
                     
                                                                                   
                                                      
                                                                                
                                                           
                                                                  
          

                                                                                                     
                                                    

                                                                                 
                                                                   
                                                    
                   
                            
                                                                   
                                                 
                                                                                
                                                                                                    
                                                                      
                                           
                                                                                         
           

                                                                                             
                                              
           
                                                                                  
                                                                           
      

                                                                                    
                                                                                               
                                             
                                                                   
                                  
                                                                                        
                                                                                                        
                                    
                                                                       
                                                             
           
                                                                           
                                           
                                                       
                                                                                   
                                                                                                 
          
                       
                                                                      
                                              
                                                                           
                                                                                     
                                                                 
                                                                                        
                        
            
                                               
                                                                
               
                                           
                                                                           
                                                                                                       
                                                                                      
                                                                                 
                           
                    
                               
                                                                              
                         
               
                                                                               
                                               
                                                  
           
                                                                           
                                                                                      
          
end ibp

end AnomDiss
