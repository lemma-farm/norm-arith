/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.Site
public import FroehlichSpencer.Surface.Laplacian
public import FroehlichSpencer.Surface.DirichletLaplacian
public import FroehlichSpencer.Surface.Hamiltonian
public import FroehlichSpencer.Surface.HamiltonianHermitian
public import FroehlichSpencer.Surface.FiniteEigenvalueCount
public import FroehlichSpencer.Surface.BoundedDensityLaw
public import FroehlichSpencer.Surface.ConfigurationSpace
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Infra.Stieltjes.EigenvalueKernel
public import FroehlichSpencer.Infra.Wegner.Averaging
public import FroehlichSpencer.Infra.Ergodic.Basic
public import Mathlib
/-!
# Averaged eigenvalue measures of the finite-volume Hamiltonians

Glue between the IDS statement and the generic infrastructure: the cube, the normalized
eigenvalue counting measure of `H_Λ(v)`, the kernel `v ↦ idsMeasure ν Λ v`, and the averaged
Wegner bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set FroehlichSpencer.Infra

namespace FroehlichSpencer.IDS

   
                                          
  
                                             
                                                                 

                                                                      
       
                                             

theorem isHermitian_neg_dirichletLaplacian (ν : ℕ) (Λ : Finset (Site ν)) :
    (-dirichletLaplacian ν Λ).IsHermitian := by
  have h := hamiltonian_isHermitian ν Λ 0
  unfold hamiltonian at h
  simpa using h

/-- The normalized eigenvalue counting measure of `H_Λ(v)`. -/
noncomputable def idsMeasure (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) : Measure ℝ :=
  eigenvalueMeasure (hamiltonian_isHermitian ν Λ v)

instance (ν : ℕ) (Λ : Finset (Site ν)) (v : Site ν → ℝ) : IsFiniteMeasure (idsMeasure ν Λ v) := by
  unfold idsMeasure; infer_instance

                                                                                       
                                                                    
                                               
                   
                                                

                                                                                    
                                                                                        
                   
                                        
                              
         

                                         
noncomputable def idsKernel (ν : ℕ) (Λ : Finset (Site ν)) : Kernel (Site ν → ℝ) ℝ :=
  eigenvalueKernel (isHermitian_neg_dirichletLaplacian ν Λ) (Subtype.val : {x // x ∈ Λ} → Site ν)

                                                                        
                                            
                             
                             
                               
                    
       

instance (ν : ℕ) (Λ : Finset (Site ν)) : IsFiniteKernel (idsKernel ν Λ) := by
  unfold idsKernel; infer_instance

                                                                                         
                                                                                                 
                                                                                            
                                    
                                                   
                                               
                                                                            
                                      
                                                                     
                                                
                                                                                           
                                                                                          
                                              
                                             
                                     
                                                            
                                                
                                                                       
                                                                                            
                        
             
                                                                                         
                                          
                                                                     
                                  
             
                                          
           
                 
                                                                
                                                                               
                                     
                 
                                                                                           
                    
                                               
                                                                  
                   
                                                                              
               
                                                                               
                                                   

end FroehlichSpencer.IDS
