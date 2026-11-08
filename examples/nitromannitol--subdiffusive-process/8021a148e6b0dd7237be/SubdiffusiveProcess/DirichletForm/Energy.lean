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

                                                                 
                           

                                                                        
                                                                           
                                                           
                                                                                  
                                                                       
                       
                                                                   
                                                                  
                                    
                                                         
                                                                         
           
                                                     
                                                                   
                                                 
                                                            
                                                                                  
                                                  
                                                                                         
                                                        
                                                   

                                                                           
                                                                     
                            

                                                
                                                                       
                                                                        
theorem norm_le_of_ae_indicator_bound {f : Lp ℝ 2 m} {S : Set X} (hS : MeasurableSet S)
    (hSfin : m S ≠ ⊤) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂m, ‖f x‖ ≤ S.indicator (fun _ => C) x) :
    ‖f‖ ≤ C * Real.sqrt ((m S).toReal) := by
  have hmono : eLpNorm (⇑f) 2 m ≤ eLpNorm (S.indicator fun _ => C) 2 m := by
    refine eLpNorm_mono_ae (Lp.aestronglyMeasurable f) ?_
    filter_upwards [hbound] with x hx
    refine hx.trans ?_
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have hind := eLpNorm_indicator_const (μ := m) (c := C) hS.nullMeasurableSet
    (p := 2) (by norm_num) (by norm_num)
  have hfin : eLpNorm (S.indicator fun _ => C) 2 m ≠ ⊤ := by
    rw [hind]
    refine ENNReal.mul_ne_top (by simp) ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSfin
  rw [Lp.norm_def]
  refine (ENNReal.toReal_mono hfin hmono).trans ?_
  rw [hind, ENNReal.toReal_mul]
  have h1 : (m S ^ (1 / (2 : ℝ≥0∞).toReal)).toReal = Real.sqrt ((m S).toReal) := by
    rw [← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
    norm_num
  rw [h1]
  have h2 : ((‖C‖ₑ : ℝ≥0∞)).toReal = C := by
    simp [enorm_eq_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC]
  rw [h2]

                                                                         

                                                                          
                                                                              
                                                                        
                        
                                                                    
                                                                    
                       
                                                                   
                                                                      
                                                                                
                            
                                                                
                                                                                              
                                                          
                                                                                            
                                           
                                       
                                                                     
                                                       
                                        
                                                                 
                                                             
                    
                              
                                                                        
                                              
                                      
                                                                                       
                                                    
                                                  
                             
                                                               
                                                
                                                                                 
                                                    
                      
                                            
                                                                                     
                                                                            
                      
                                                                    
                                       
                 
                             
                            
                                                                                       
                          
                                                      
                                                                       
                            
                                                                                      
                  

                                                                               
                                                                             
                                               

                                                         
                                                                                
                                                                             
                                                                 
                                                                                 
                                                                               
                                                          
                                           
                                                                                
                                               
                                                        
                                                                
              
                                                       
                                                                             
                                         
                                           
                                                                    
                                                                      
                           
                                           
                                                       
                                                                       
                                 
            
                                                 
                                                                    
                                                                
                                                            
            
                                                              
                                                    
                                                  
                              
                                 
                                       
                                                   
                                                              
           
                     

end ClosedForm

                                      
                                                             
                                                                                  

                                                                  
                                                         
         
                                                   

                                                                     
                                                                           

                                                                                             
                                                                        
                                                        
                                                                               
                                                                               
                                                                      
                                                           
                                                                              
                                                       
                                                                                   

                                                                       
                                                                                           
                                                              
                                   
                                                                      
                                                                      
                                                                       
                                                                                             
                                                         
                                                                    
                                                                                  
                         
                                                                      
                               
                                         

end SubdiffusiveProcess.DirichletForm
