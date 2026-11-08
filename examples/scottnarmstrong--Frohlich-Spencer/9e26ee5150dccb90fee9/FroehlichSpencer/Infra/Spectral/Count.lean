/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib

/-!
# Eigenvalue counting for finite Hermitian matrices

For a Hermitian matrix `H : Matrix ι ι ℂ` over a finite index type, `eigenvalueCount hH E` is the
number of eigenvalues of `H` that are `≤ E`, counted with multiplicity, and `eigenvalueCountLT hH E`
the number that are `< E`.

The spectral subspace `spectralSubspace hH S` is the span of the
eigenvectors whose eigenvalue lies in `S : Set ℝ`.

The counting function is the object `N_Λ(E, v)` of Fröhlich–Spencer (1983), defined after (1.9)
and used in Appendix C (Fröhlich–Spencer (1983)), but nothing here is specific to that
setting: the index type and the matrix are arbitrary.

All definitions use Mathlib's `Matrix.IsHermitian.eigenvalues` and
`Matrix.IsHermitian.eigenvectorBasis`; by proof irrelevance they depend on `H` only
(`eigenvalueCount_congr`).
-/

@[expose] public section

open Matrix Finset

namespace FroehlichSpencer.Infra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}

/-- The number of eigenvalues of a Hermitian matrix that are `≤ E`, counted with multiplicity. -/
noncomputable def eigenvalueCount (hH : H.IsHermitian) (E : ℝ) : ℕ :=
  #{i | hH.eigenvalues i ≤ E}

                                                                                                 
                                                                       
                             

                                                                                              
               
noncomputable def spectralSubspace (hH : H.IsHermitian) (S : Set ℝ) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ ((fun i => ⇑(hH.eigenvectorBasis i)) '' {i | hH.eigenvalues i ∈ S})

/-- The fixed relabelling `ι ≃ Fin (card ι)` under which Mathlib's `eigenvalues` (indexed by `ι`)
become the increasing list `eigenvaluesAsc`. It depends on `ι` only, not on the matrix. -/
noncomputable def ascIndex (ι : Type*) [Fintype ι] : ι ≃ Fin (Fintype.card ι) :=
  (Fintype.equivOfCardEq (Fintype.card_fin _)).symm.trans Fin.revPerm

/-- The eigenvalues of a Hermitian matrix in increasing order: `eigenvaluesAsc hH k` is the
`(k + 1)`-st smallest eigenvalue, counted with multiplicity. (Mathlib's `eigenvalues₀` lists them
in decreasing order.) -/
noncomputable def eigenvaluesAsc (hH : H.IsHermitian) (k : Fin (Fintype.card ι)) : ℝ :=
  hH.eigenvalues₀ k.rev

                                                                                                
                                                      
              

                                                                                        
                                                                    
              

                                                                                       
                                                                      
              

theorem eigenvaluesAsc_congr (hH : H.IsHermitian) (hH' : H'.IsHermitian) (h : H = H') :
    eigenvaluesAsc hH = eigenvaluesAsc hH' := by
  subst h; rfl

variable (hH : H.IsHermitian)

theorem eigenvalues_eq_eigenvaluesAsc_ascIndex (i : ι) :
    hH.eigenvalues i = eigenvaluesAsc hH (ascIndex ι i) := by
  simp [eigenvaluesAsc, ascIndex, IsHermitian.eigenvalues]

theorem eigenvaluesAsc_monotone : Monotone (eigenvaluesAsc hH) := fun _ _ hkl =>
  hH.eigenvalues₀_antitone (Fin.rev_le_rev.mpr hkl)

                                                                                  
                    

                                                                                      
                    

                                                                               
                                                                                                  

                                                                                   
                          
                                                                              

                                                      
                                                    
                                                                                     

                                                                               
                                                     
                          
                                                                              

                                                                                      
                            
                                                                
                                                                                               
                                                                   
           
         
                                                                      
               
                    
                            
                 
             
                                        
                       
                                      
                        
                  
                             

                                                                                                 
                                                              
                                           
                                                       
                                                            
                                                       
                

end FroehlichSpencer.Infra
