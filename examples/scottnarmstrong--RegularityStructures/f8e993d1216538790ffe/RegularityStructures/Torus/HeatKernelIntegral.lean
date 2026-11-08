/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelFacts
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Gaussian periodisation on the three-torus

The normalization and locally uniform convergence of the periodised Gaussian are recorded here. This
is the unfolding of the periodised heat kernel (2.1) of the statement.
-/

public section

open MeasureTheory Real Set Submodule

namespace RegularityStructures

noncomputable def integerLatticeAddEquiv :
    (Fin 3 → ℤ) ≃ (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup := by
  let e : (Fin 3 → ℤ) →
      (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
    fun k => ⟨fun i => (k i : ℝ), by
      change (fun i => (k i : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))
      rw [Module.Basis.mem_span_iff_repr_mem]
      simp [Pi.basisFun_repr]
      ⟩
  apply Equiv.ofBijective e
  constructor
  · intro k l h
    have h' : (fun i => (k i : ℝ)) = fun i => (l i : ℝ) := congrArg Subtype.val h
    funext i
    exact_mod_cast congrFun h' i
  · intro x
    have hx' : ∀ i, ∃ n : ℤ, x.1 i = (n : ℝ) := by
      have hmem := (Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ (x : Fin 3 → ℝ)
        |>.mp x.2
      simp [Pi.basisFun_repr] at hmem
      intro i
      rcases hmem i with ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    choose k hk using hx'
    refine ⟨k, ?_⟩
    apply Subtype.ext
    funext i
    dsimp [e]
    exact (hk i).symm

theorem integerLatticeAddEquiv_apply (k : Fin 3 → ℤ) (i : Fin 3) :
    (integerLatticeAddEquiv k).1 i = (k i : ℝ) := by
  rfl

noncomputable instance integerLatticeCountable :
    Countable (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
  Countable.of_equiv (Fin 3 → ℤ) integerLatticeAddEquiv

theorem fundamentalDomain_ae_eq_pi_Ioc :
    ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3)) =ᵐ[volume]
      Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1) := by
  rw [ZSpan.fundamentalDomain_pi_basisFun]
  have hco := Measure.univ_pi_Ico_ae_eq_Icc
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun _ : Fin 3 => (0 : ℝ)) (g := fun _ : Fin 3 => (1 : ℝ))
  have hoc := Measure.univ_pi_Ioc_ae_eq_Icc
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun _ : Fin 3 => (0 : ℝ)) (g := fun _ : Fin 3 => (1 : ℝ))
  have h := hco.trans hoc.symm
  simpa only [volume_pi] using h

                                                          
                                  
                                                        
                                            
             
                                                         
           
                                           
                                      
                                         
                                                                        
            
                                 
                                                         
           
                                                   
                     
                                                   
                                                               
                                              
                                                         
                                                                      
                         
                                                                         

                                                                     
                                         
                                  
                                                            
           
                                                                              
                                     
           
                                                            
                                                             
                                                                             
                                              
                                           
                                                                          
                                   
                                             
                                         
                                  
                                                
                                          
                        
                      
          
                                                     
      

                                                                       
                                         
                                                                                
                                            
                                                      
                
         
                          
     

theorem torusRep_torusProj_of_mem_Ico {x : Fin 3 → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) : torusRep (torusProj x) = x := by
  funext i
  dsimp [torusRep, torusProj]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa using hx i))

                                                                     
                                                                      
                                                                         
                                                              
                                                                            
                                                                         
                                    
                  
                                                                                         
                   
                 
                  
                                                   
                
                                            
                                                             
                                                 
                  
                                     
             
                                            
                                                                                        
                                                          
                
                   
                                                  
                                               
                       
                                                                      
                                         
                                                       
              
           
                                         
                                                               
                                                        
                      
                                       
                                                   
                         
                                                                       
              
                                       
                                                                                       
                                                       
                               
                                        
                                                                
                                 
           
                                                             
                                                                        
                                         
      
                      
                                
                                                                    
                                                                
          
          
                                                            
                                                                              
                                    
                                                            
                                                                                                    
                             
                                    
                                                                             
                                               
                          
                 
                 
                  
                 
                  
                                                       

                                                  
                                          
                                        
                                                        
                                                         
             
                                                                                   
                                                                         
                                                                              
                                                                 
                                                         
                                                                                          
                                     
                                                                                    
                                   
                                                
                                          
                                                         
                                                     
                              

end RegularityStructures

end
