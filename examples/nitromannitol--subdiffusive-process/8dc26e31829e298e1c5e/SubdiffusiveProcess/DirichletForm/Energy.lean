/-
# The extended energy functional, the order on forms, and Mosco convergence
-/
module

public import SubdiffusiveProcess.DirichletForm.Basic
public import Mathlib
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

open scoped Classical in
/-- The energy functional extended to all of `L²(X, m)` by `⊤` off the domain. -/
noncomputable def energy (E : ClosedForm m) (u : Lp ℝ 2 m) : EReal :=
  if u ∈ E.domain then (E.form u u : EReal) else ⊤

variable (E F : ClosedForm m)

@[simp] theorem energy_of_mem {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    E.energy u = (E.form u u : EReal) := by
  simp [energy, hu]

@[simp] theorem energy_of_notMem {u : Lp ℝ 2 m} (hu : u ∉ E.domain) : E.energy u = ⊤ := by
  simp [energy, hu]

theorem energy_lt_top_iff (u : Lp ℝ 2 m) : E.energy u < ⊤ ↔ u ∈ E.domain := by
  by_cases hu : u ∈ E.domain
  · simp [hu, EReal.coe_lt_top]
  · simp [hu]

theorem mem_domain_of_energy_lt_top {u : Lp ℝ 2 m} (hu : E.energy u < ⊤) : u ∈ E.domain :=
  (E.energy_lt_top_iff u).mp hu

                                                           
                            
                                                                
             

@[simp] theorem energy_zero : E.energy 0 = 0 := by
  simp [E.form_zero_left E.domain.zero_mem]

                                                                                 
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

theorem LEWithConst.rfl (E : ClosedForm m) : LEWithConst E E 1 :=
  fun u hu => ⟨hu, by simp⟩

                                                                        
                                                                           
                                                           
                                                                                  
                                                                       
                       
                                                                   
                                                                  
                                    
                                                         
                                                                         
           
                                                     
                                                                   
                                                 
                                                            
                                                                                  
                                                  
                                                                                         
                                                        
                                                   

                                                                           
                                                                     
                            

                                                
                                                                       
                                                                        
                                                                                       
                                          
                                                            
                                            
                                                                            
                                                         
                                     
                      
                         
                       
                                                                             
                                        
                                                            
             
                                          
                                                           
                  
                                                  
                               
                                                                                   
                                                 
            
         
                                            
                                                              
         

                                                                         

                                                                          
                                                                              
                                                                        
                        
                                                                    
                                                                    
                       
                                                                   
                                                                      
                                                                                
                            
                                                                
                                                                                              
                                                          
                                                                                            
                                           
                                       
                                                                     
                                                       
                                        
                                                                 
                                                             
                    
                              
                                                                        
                                              
                                      
                                                                                       
                                                    
                                                  
                             
                                                               
                                                
                                                                                 
                                                    
                      
                                            
                                                                                     
                                                                            
                      
                                                                    
                                       
                 
                             
                            
                                                                                       
                          
                                                      
                                                                       
                            
                                                                                      
                  

                                                                               
                                                                             
                                               

                                                         
                                                                                
                                                                             
                                                                 
                                                                                 
                                                                               
                                                          
                                           
                                                                                
                                               
                                                        
                                                                
              
                                                       
                                                                             
                                         
                                           
                                                                    
                                                                      
                           
                                           
                                                       
                                                                       
                                 
            
                                                 
                                                                    
                                                                
                                                            
            
                                                              
                                                    
                                                  
                              
                                 
                                       
                                                   
                                                              
           
                     

end ClosedForm

                                      
                                                             
                                                                                  

                                                                  
                                                         
         
                                                   

                                                                     
                                                                           

                                                                                             
                                                                        
                                                        
                                                                               
                                                                               
                                                                      
                                                           
                                                                              
                                                       
                                                                                   

                                                                       
                                                                                           
                                                              
                                   
                                                                      
                                                                      
                                                                       
                                                                                             
                                                         
                                                                    
                                                                                  
                         
                                                                      
                               
                                         

end SubdiffusiveProcess.DirichletForm
