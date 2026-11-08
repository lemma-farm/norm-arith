module

public import RequestProject.Parameters

/-!
# Staged advection–diffusion problems (toward Lemma 5.6)

Uniqueness of classical scalar solutions (from the maximum principle), Hölder regularity of
data, existence of solutions on a single stage (from External Result 1.6), and the chaining of
stages `I_j = [s_j, s_j + δ_j]` (drift `D_j`) and `J_j = [s_j + δ_j, s_{j+1}]` (no drift).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace AnomDiss

/-! ### Stage times -/

                                       

                                                                          
                                                  

                                                    
                                                                       
                                 

                                                                    

                                                  
                                                           
            

                                                  
                                                           
            

                                                     

section ops
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                                                     
                                                                                
                                                   

end ops

/-! ### Uniqueness -/

                                                                                            
                                                                
                                                                            
                                                                             
                                                                           
                                     
                                        
                                                                                              
                                                      
                                                        
                                                                    
                                            
                                                                           
                                                              
                                                                     
                                          
              
            
                      
                                            
              
                
                            
                             
                                  
                                                                                   
                    
                                                                        
                                                                                             
                                     
                                                                                                     
                                                             
                                                                                
                          
                                   
                                               
                                                                                                 
                                                                                  
                             
                                      
            

                                                        

section congr
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dt_congr {T : ℝ} {u u' : ℝ → Pt d → E} (h : ∀ t ∈ Icc 0 T, u' t = u t) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : Pt d) : dt T u' t x = dt T u t x := by
  unfold dt
  exact derivWithin_congr (fun s hs => by simp [h s hs]) (by simp [h t ht])

lemma IsParabolicC12.congr {T β : ℝ} {u u' : ℝ → Pt d → E} (hu : IsParabolicC12 T β u)
    (h : ∀ t ∈ Icc 0 T, u' t = u t) : IsParabolicC12 T β u' := by
  have hd : ∀ t ∈ Icc 0 T, ∀ x, dt T u' t x = dt T u t x := fun t ht x => dt_congr h ht x
  obtain ⟨h1, h2, ⟨C3, h3⟩, ⟨C4, h4⟩, ⟨C5, h5⟩, h6, h7, h8, h9⟩ := hu
  refine ⟨fun t ht => by rw [h t ht]; exact h1 t ht, fun x t ht => ?_, ⟨C3, fun t ht x => ?_⟩,
    ⟨C4, fun t ht x => ?_⟩, ⟨C5, fun t ht s hs x y => ?_⟩, fun i => ?_, fun i => ?_,
    fun i j => ?_, fun i j => ?_⟩
  · exact (h2 x t ht).congr (fun s hs => by simp [h s hs]) (by simp [h t ht])
  · rw [h t ht]; exact h3 t ht x
  · rw [hd t ht]; exact h4 t ht x
  · rw [hd t ht, hd s hs]; exact h5 t ht s hs x y
  · obtain ⟨C, hC⟩ := h6 i; exact ⟨C, fun t ht x => by dsimp only; rw [h t ht]; exact hC t ht x⟩
  · obtain ⟨C, hC⟩ := h7 i
    exact ⟨C, fun t ht s hs x => by dsimp only; rw [h t ht, h s hs]; exact hC t ht s hs x⟩
  · obtain ⟨C, hC⟩ := h8 i j; exact ⟨C, fun t ht x => by dsimp only; rw [h t ht]; exact hC t ht x⟩
  · obtain ⟨C, hC⟩ := h9 i j
    exact ⟨C, fun t ht s hs x y => by dsimp only; rw [h t ht, h s hs]; exact hC t ht s hs x y⟩

lemma IsClassicalScalar.congr {T ν : ℝ} (hT : 0 ≤ T) {v : ℝ → Pt d → Pt d} {θ₀ : Pt d → E}
    {θ θ' : ℝ → Pt d → E} (hθ : IsClassicalScalar T ν v θ₀ θ)
    (h : ∀ t ∈ Icc 0 T, θ' t = θ t) : IsClassicalScalar T ν v θ₀ θ' := by
  obtain ⟨β, hβ0, hβ1, reg⟩ := hθ.regular
  refine ⟨fun t ht => by rw [h t ht]; exact hθ.periodic t ht, ⟨β, hβ0, hβ1, reg.congr h⟩,
    by rw [h 0 ⟨le_rfl, hT⟩]; exact hθ.init, fun t ht x => ?_⟩
  rw [dt_congr h ht, h t ht]; exact hθ.eqn t ht x

end congr

/-! ### Hölder regularity of data -/

                                                               
                                                                              
                                                                                           
                                                         
                               
                                
                                               
                              
                                                                           
                                                                   
                                       
                                                                        
                                                     
                                                                                      
                                                                                  

                                                                  
                                                                                             
                                                                               
                                                                                      
           
                                                  
                  
                                  
                                  
                          
                                           
                                                         
                         
                                    
                                                    
                                                                 
                                      
                                                         
                                   
                                                   
                   
                                                      
                                                       
                                           
                                             

                                                         
                                                                                      
                                                              
                                                                            
                                                   
                                          
             
                                                                         
                         
                              
                                                                         
                                                          
                                                         
                                                                                              
                             
                  

                                                               
                                                                              
                                                                                  
                                                     
                                                                                                   
             
                                                                      
                                      
                                                                       
                                                                      
                                                          
                                                
                                                    
                       
                                                              
                                                                         
                                       
                                                                        
                                                     
                                                                                      
                                                                                  

                                          
                                                                                                           
                                                                                              
                                                                                           

                                                                              
                                                                             
                                                                   
                                                                                             
                                                                        
                                                                        
                                                                                                
             
                   

                          

                                                                                           
                                                                                              
                     
                                                                      
                                 
                                  
                                                                           
                                                                                                

                                               
                                                        
                                                                           
                                                                                           
                                 
                                                                   
                  
                    
                   
                  
                                        
                                      
                  
                         
                                                   
                
                                  
                  
                              
                                   
                                                      
                                             
                               
                                                    
                                                                             
                          
                                                                                              
                                                                                           
                          
                                     

                                                             
lemma IsClassicalScalar.abs_le {T ν : ℝ} (hν : 0 ≤ ν) {v : ℝ → Pt 2 → Pt 2} {θ₀ : Pt 2 → ℝ}
    {θ : ℝ → Pt 2 → ℝ} (hθ : IsClassicalScalar T ν v θ₀ θ) {M : ℝ} (hM : ∀ x, |θ₀ x| ≤ M) :
    ∀ t ∈ Icc 0 T, ∀ x, |θ t x| ≤ M := by
  obtain ⟨β, -, -, reg⟩ := hθ.regular
  exact max_principle_abs T ν hν v θ reg.continuousOn hθ.periodic reg.smooth_x reg.diff_t
    hθ.eqn M (by rw [hθ.init]; exact hM)

                                                       
                                                                            
                                                                      
                                                                         
                                                                                                
                          
                                
                   
                                                                         
                          
                                
                   
                                                                         

                                                                   
                                                                            
                                                                          
                                                                        
                                                        
                                                         
                          
                                            
                          
                                            

                                               

                                                                                              
                               
                                                                                     
                                                                          
                             
                                                                        
                      
                       
                                                           
                                                            
                                                                                 
                                             
                                                                                      
                                                                    
                                                                                    
                                   
                                                                          
             
                                                                                    
                                                                
                                                    
                
                                                        
                                                                          
                                                
                                                                                      
                                                                    
                                                     
              
                                          
                                                                                          

                                                                                           
                                                                        
                                                                           
                                                                
                                                            
                                                   
                                                                              
                                                                                                  
                                                                        
                                                                                          
                               
                                             
                                      
     

                                                                                             
                                                                            
                                                    
                                                                         
                                           
               
                                                
                              
                                                                             
                                                                                  
                         

                                                                 
                                                                
                                                                                        
                                                                        
                       
                                                                
                                                                                   
                                                           
                  
                                                                                     
                                                                          
            
                                        
                                                                  
                                           
                                                 
                                                                                          
                          
                                                              
                                                              
                                   
             
                                                         
                                           
                   
                                                                                              
                                                                                                  
                                                                                            
               
                              
                               
                 
                   
                                                                   
                 

                                                                 
                                                               
                                                                         
                                                  
                                                          
                                                                    
                                                                                
                                          
                                                                               
                                                         
                                                               
                                  
                          
                                      
                                                           
                              
                          
                                                                                                      
                                                                            

                                           

section existence

variable (ν : ℝ) (D : ℕ → ℝ → Pt 2 → Pt 2) (θ₀ : Pt 2 → ℝ)

                                                            
                                                                           
                                                                                     

                                                
                            
           
                                  
                                                                                            

                                             
                                                                                 

                                            
                                                                                              

                 
                                 
                                           
                                                 
                                                                                           

end existence

                                                                              
                                                                   
                                                                                             
                                                                    
                                                                                                 
                                                                             

                                                                      
                                           

                                                                        
                                    
                                                    
                              
                                               
                           
                                                   
                    
          

                                                                  
                                                                         
                             
                                                                         
                                                                                                
                                                                  
                                    
                                                                    
                                   
                                                                                   
                                                        
                                                                                  
                                                        
                                                                                                   
                  
                    
                   
                  
                                                          
                                                             
                                                
                  
                                        
                                                                                       
                                                     
                                                                          
                                                                    
                
                                                                     
                                                                        
                                                 
                                                                                           
               
                                                                                   
                                                                                             
                                                                         
                                                                   
                           
                                          
                                                      
                                                     
                        
                                                              
                                                               
                                                                                
                                        
                                                                                   
                
                    
                                                        
                          
                          
                               
                                
                                                                                         
                
                                                                            
                                     
                                           
               
                                                                                     
                     
                                                                                       
                                  
                                                                      
                
                                           
               
                           
                                                                   
                                                
                                                                          
                                                                                      
                                                   
                 
                                 
                                                                              
                                                      
                                                                                  
                                                          
                                                                   
                                               
                       
                                                               
                                                                                     
                                                   
                                                                      
                                                 
                     
                                                                     
                                  
                           
                         
                                                                            
                               
                   
                                          
                                          

end AnomDiss
