/-
# The extended energy functional, the order on forms, and Mosco convergence
-/
module

public import SubdiffusiveProcess.DirichletForm.Basic

@[expose] public section

/-!
# Extended energy, order of forms, Mosco convergence

For a closed form `E` we extend `u ↦ E(u, u)` to all of `L²(X, m)` by `⊤`
outside the domain (`SubdiffusiveProcess.DirichletForm.ClosedForm.energy`).  This makes the domain
readable off the functional and lets the order of forms and Mosco convergence be
stated without side conditions.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm.energy`: `E(u) ∈ EReal`, equal to `⊤` off `D(E)`.
* the `Preorder` on `ClosedForm m` given by `E ≤ F ↔ ∀ u, E(u) ≤ F(u)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.LEWithConst`: `E ≤ C · F` on `D(F)`.
* `SubdiffusiveProcess.DirichletForm.TendstoWeakly`: weak convergence in `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.MoscoConverges`: Mosco convergence (weak liminf bound and
  existence of a strong recovery sequence).

## References

* U. Mosco, *Composite media and asymptotic Dirichlet forms*, J. Funct. Anal.
  123 (1994).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

namespace SubdiffusiveProcess.DirichletForm

namespace ClosedForm

                        
                                                                                 
                                                                     
                                                  

variable (E F : ClosedForm m)

                                                                  
                                           
                   

                                                                                          
                   

                                                                              
                            
                               
             

                                                                                          
                               

                                                           
                            
                                                                
             

                                                  
                                           

                                                                                 
def LEWithConst (E F : ClosedForm m) (C : ℝ) : Prop :=
  ∀ u ∈ F.domain, u ∈ E.domain ∧ E.form u u ≤ C * F.form u u

theorem LEWithConst.mem_domain {E F : ClosedForm m} {C : ℝ} (h : LEWithConst E F C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) : u ∈ E.domain := (h u hu).1

theorem LEWithConst.form_le {E F : ClosedForm m} {C : ℝ} (h : LEWithConst E F C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) : E.form u u ≤ C * F.form u u := (h u hu).2

theorem LEWithConst.trans {E F G : ClosedForm m} {C D : ℝ} (hC : 0 ≤ C)
    (h₁ : LEWithConst E F C) (h₂ : LEWithConst F G D) : LEWithConst E G (C * D) := by
  intro u hu
  refine ⟨h₁.mem_domain (h₂.mem_domain hu), ?_⟩
  calc E.form u u ≤ C * F.form u u := h₁.form_le (h₂.mem_domain hu)
    _ ≤ C * (D * G.form u u) := mul_le_mul_of_nonneg_left (h₂.form_le hu) hC
    _ = C * D * G.form u u := by ring

                                                                 
                           

                                                                        
                                                                           
                                                           
theorem tendsto_form_of_tendsto_energyNormSq {E : ClosedForm m} {u : ℕ → Lp ℝ 2 m}
    {w v : Lp ℝ 2 m} (hu : ∀ n : ℕ, u n ∈ E.domain) (hw : w ∈ E.domain)
    (hv : v ∈ E.domain)
    (h : Tendsto (fun n => E.energyNormSq (u n - w)) atTop (𝓝 0)) :
    Tendsto (fun n => E.form (u n) v) atTop (𝓝 (E.form w v)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ n : ℕ, dist (E.form (u n) v) (E.form w v) ≤
      Real.sqrt (E.energyNormSq (u n - w)) * Real.sqrt (E.form v v) := by
    intro n
    rw [Real.dist_eq, ← E.form_sub_left (hu n) hw hv]
    refine (E.abs_form_le (E.domain.sub_mem (hu n) hw) hv).trans ?_
    have := E.form_le_energyNormSq (u := u n - w)
    have hnn := E.form_nonneg _ (E.domain.sub_mem (hu n) hw)
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt this) (Real.sqrt_nonneg _)
  refine squeeze_zero (fun n => dist_nonneg) hb ?_
  have hs : Tendsto (fun n : ℕ => Real.sqrt (E.energyNormSq (u n - w))) atTop (𝓝 0) := by
    simpa using! (Real.continuous_sqrt.tendsto 0).comp h
  simpa using hs.mul_const (Real.sqrt (E.form v v))

                                                                           
                                                                     
                            

                                                
                                                                       
                                                                        
                                                                                       
                                          
                                                            
                                            
                                                                            
                                                         
                                     
                      
                         
                       
                                                                             
                                        
                                                            
             
                                          
                                                           
                  
                                                  
                               
                                                                                   
                                                 
            
         
                                            
                                                              
         

                                                                         

                                                                          
                                                                              
                                                                        
                        
                                                                    
                                                                    
                       
                                                                   
                                                                      
                                                                                
                            
                                                                
                                                                                              
                                                          
                                                                                            
                                           
                                       
                                                                     
                                                       
                                        
                                                                 
                                                             
                    
                              
                                                                        
                                              
                                      
                                                                                       
                                                    
                                                  
                             
                                                               
                                                
                                                                                 
                                                    
                      
                                            
                                                                                     
                                                                            
                      
                                                                    
                                       
                 
                             
                            
                                                                                       
                          
                                                      
                                                                       
                            
                                                                                      
                  

                                                                               
                                                                             
                                               

                                                         
                                                                                
                                                                             
                                                                 
                                                                                 
                                                                               
                                                          
                                           
                                                                                
                                               
                                                        
                                                                
              
                                                       
                                                                             
                                         
                                           
                                                                    
                                                                      
                           
                                           
                                                       
                                                                       
                                 
            
                                                 
                                                                    
                                                                
                                                            
            
                                                              
                                                    
                                                  
                              
                                 
                                       
                                                   
                                                              
           
                     

end ClosedForm

                                      
                                                             
                                                                                  

                                                                  
                                                         
         
                                                   

                                                                     
                                                                           

                                                                                             
                                                                        
                                                        
                                                                               
                                                                               
                                                                      
                                                           
                                                                              
                                                       
                                                                                   

                                                                       
                                                                                           
                                                              
                                   
                                                                      
                                                                      
                                                                       
                                                                                             
                                                         
                                                                    
                                                                                  
                         
                                                                      
                               
                                         

end SubdiffusiveProcess.DirichletForm
