/-
# Closed symmetric forms and Dirichlet forms on `L²`

This file is the base of a self-contained, reusable Dirichlet-form library.  It
imports only Mathlib, uses no carrier of the ambient project, and is written so
that the directory `SubdiffusiveProcess/DirichletForm/` can be lifted into a
standalone Lake package without changes.
-/
module

public import Mathlib
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

/-!
# Closed symmetric forms and Dirichlet forms

Let `m` be a measure on a measurable space `X`.  A **closed form** on `L²(X, m)`
is a densely defined, symmetric, nonnegative bilinear form `E` whose domain
`D(E)` is a submodule of `L²(X, m)` complete for the energy norm
`E₁(u) = E(u, u) + ‖u‖²`.  A **Dirichlet form** is a closed form on which the
unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm m`: a densely defined, symmetric, nonnegative,
  closed bilinear form on `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.energyInner`, `SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq`:
  the energy inner product `E₁(u, v) = E(u, v) + ⟪u, v⟫` and `E₁(u) = E₁(u, u)`.
* `SubdiffusiveProcess.DirichletForm.IsNormalContraction`: `T : ℝ → ℝ` with `T 0 = 0` and
  `|T s - T t| ≤ |s - t|`.
* `SubdiffusiveProcess.DirichletForm.unitTruncation`: the unit contraction `t ↦ (t ⊓ 1) ⊔ 0`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.OperatesOn`: `T` operates on `E`, i.e. `T ∘ u` stays
  in `D(E)` and does not increase the energy.
* `SubdiffusiveProcess.DirichletForm`: a closed form on which `unitTruncation` operates.
* `SubdiffusiveProcess.DirichletForm.HasNormalContractions`: the Fukushima–Oshima–Takeda statement
  that *every* normal contraction operates on a Dirichlet form.

## Implementation notes

The bilinear form is carried as a total function `Lp ℝ 2 m → Lp ℝ 2 m → ℝ`; every
axiom is restricted to the domain, so the values off the domain carry no
information.  This keeps statements free of subtype coercions and matches the
way a form defined by a dual (resolvent) expression is met in practice.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd edition, de Gruyter, 2011.
-/

open MeasureTheory Filter Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]

namespace SubdiffusiveProcess.DirichletForm

/-- The unit contraction `t ↦ (t ⊓ 1) ⊔ 0` of the real line. -/
def unitTruncation (t : ℝ) : ℝ := max (min t 1) 0

                                                                             

                                                                                           
                                                                             
                                                                       
                                                      
                                               
                    
                                               
                                            

                                                                               
                              

                                                                                         
                                                                        
                                                        
structure ClosedForm (m : Measure X) where
  /-- The form domain `D(E)`, a linear subspace of `L²(X, m)`. -/
  domain : Submodule ℝ (Lp ℝ 2 m)
  /-- The bilinear form `E(u, v)`.  Values outside `domain` carry no
  information: every axiom below is restricted to `domain`. -/
  form : Lp ℝ 2 m → Lp ℝ 2 m → ℝ
  /-- `D(E)` is dense in `L²(X, m)`. -/
  denseDomain : Dense (domain : Set (Lp ℝ 2 m))
  /-- `E(u, v) = E(v, u)`. -/
  form_symm : ∀ u ∈ domain, ∀ v ∈ domain, form u v = form v u
  /-- `E` is additive in its first argument. -/
  form_add_left : ∀ u ∈ domain, ∀ v ∈ domain, ∀ w ∈ domain,
    form (u + v) w = form u w + form v w
  /-- `E` is homogeneous in its first argument. -/
  form_smul_left : ∀ c : ℝ, ∀ u ∈ domain, ∀ v ∈ domain, form (c • u) v = c * form u v
  /-- `E(u, u) ≥ 0`. -/
  form_nonneg : ∀ u ∈ domain, 0 ≤ form u u
  /-- `E` is closed: `D(E)` is complete for the energy norm
  `E₁(u) = E(u, u) + ‖u‖²`. -/
  complete : ∀ u : ℕ → Lp ℝ 2 m, (∀ n, u n ∈ domain) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      form (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε) →
    ∃ w ∈ domain, Tendsto
      (fun n => form (u n - w) (u n - w) + ‖u n - w‖ ^ 2) atTop (𝓝 0)

namespace ClosedForm

variable {m : Measure X} (E : ClosedForm m)

/-- `E(0, v) = 0`. -/
theorem form_zero_left {v : Lp ℝ 2 m} (hv : v ∈ E.domain) : E.form 0 v = 0 := by
  simpa using E.form_smul_left 0 0 E.domain.zero_mem v hv

                     
                                                                                 
                                                                

                                              
                                                                                 
                                                                          
                                                                                  
                                                 

                                                 
                                                                    
                                                                 
                                                                                
                          

                             
                                                                                
                                     
                                             

                             
                                                                                 
                                     
                                          

                                         
                                                                                
                                                                          
                                                                        
                                          

                                         
                                                                                 
                                                                          
                                                                   
                                           

                                      
                                                                                
                                                                           
                                                                                      
                                                     
      

                                              
                                                                       
                         
                                    
                                                                
                                                                             
                                                                                  
      

                                                                              
        
                                                                                 
                                                  
                                                                                      
           
                                                                            
                                          
                 
                               
                   
               

                                                                      
                                                                              
                                                                        
                                  
                                                                                           
                             
                             
         

                                                                   
                                                                

                                                        
def energyNormSq (u : Lp ℝ 2 m) : ℝ := E.form u u + ‖u‖ ^ 2

                                                                                            
                                  

                                               
                                                                    
                                    
                            
                          
          

                                      
                                                                                           
                                        
                           

                        
                                                             
                                                
                                                                           
                                     
      

                               
                                                                                        
                                                         
                                                             

                                                  
                                                                                 
                          
                           

                                  
                                                                          
                                            
                                                           
                                                                  
                          

                         
                                                                                   
                                               
                                                                       

                                    
                                                                               
                         
                                
                                                                                   
                                                                                            
                                                                                              
        
                                                                            
      

                                                                    
                                                                                        
                                                                     
                     
                                                                                         
           
                                                                                  
                                                  
                 
                               
                   
               

                                                                              
                                                                       
                                                                                     
                                                                                           
                                         
                                                            
                                               
                             
                             
         

                                                                             
                                                         
                                                                     
                         
                                        
                                                                       
                                      
                                                                       
                                                  
                 
                                        
                                     
                                                                             
                                                                    
                                             
                                                                    
                                             
                                 
                                                                      
                                  
                          
                                                                                  
              
                                         
                                                                                        
                             
                                                                      
                        

                                                                        
                                                                       
                                             
                                        
                                                                                   
                                               
        
                                                                                    

                                                                           
                                                                         
                                                                           
                             
                                    
                                                               
                                          

                                                                               
                                                                                                
                                                                            
                                                                   
                                            
                                                     

end ClosedForm

end SubdiffusiveProcess.DirichletForm

/-- A **Dirichlet form** on `L²(X, m)`: a closed symmetric nonnegative form on
which the unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroDirichletForm`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure SubdiffusiveProcess.DirichletForm (m : Measure X) extends _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m where
  /-- The Markov property: the unit contraction operates on `E`. -/
  markov : ∀ u ∈ domain, ∀ v : Lp ℝ 2 m,
    (⇑v =ᵐ[m] fun x => _root_.SubdiffusiveProcess.DirichletForm.unitTruncation (u x)) →
    v ∈ domain ∧ form v v ≤ form u u

namespace SubdiffusiveProcess.DirichletForm

variable {m : Measure X}

                                             
                                                                
                       

                                             
                                                                           
                                                       
             
                                                                                          

                                                    
                                                                                       
                                 
                   
                                                          
                                

                                             
                                                                                    
                           
                                                   
                                           

                                                               
                                                                                    
                                                        

                                                                         
                                                                        
                                                                            
                               

                                                                             
                                              

                                                                                                    
                                                                        
                                                        
                                                                                             
                                                  
                                                                               

                                                                                
                                                                                          
                                                                              

end SubdiffusiveProcess.DirichletForm
