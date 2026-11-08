/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
Modified for enaslund/unit-distance-bound: `public import Mathlib` narrowed to
specific Mathlib modules for the Lean 4.32.0 / Mathlib 81a5d257 pin; no internal
imports to relocate; proof text unchanged. Upstream and local hashes:
third-party/aintlib/manifest.json.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Tactic

/-!
# The dual lattice of a ℤ-lattice  (SP1-AGP, leaf P.1)

The first substrate brick for `n`-dimensional Poisson summation. Mathlib has the *set-level*
dual of a submodule with respect to a bilinear form (`LinearMap.BilinForm.dualSubmodule`) and
the structural identity `dualSubmodule_span_of_basis` (the dual of a lattice is spanned by the
dual basis), but **nothing** connecting it to `IsZLattice` / `ZLattice.covolume`. Here we
specialise it to the inner-product bilinear form `innerₗ V` of a finite-dimensional real inner
product space and record the foundational API.

## Main definitions / results (this file)
* `DedekindResidue.dualZLattice L` — the dual lattice `L♯ = {y | ∀ x ∈ L, ⟪y, x⟫ ∈ ℤ}`.
* `DedekindResidue.mem_dualZLattice` — its membership characterisation.
* `DedekindResidue.innerₗ_nondegenerate` — the inner-product bilinear form is nondegenerate.
* `DedekindResidue.dualZLattice_eq_span` — `L♯ = span ℤ (dual basis)`; the structural lever that
  makes `L♯` a ℤ-lattice (via `instIsZLatticeRealSpan`) and feeds the covolume reciprocal.

## Next targets (SP1-AGP, tracked in `.mathlib-quality/tickets.md`)
* `IsZLattice ℝ (dualZLattice L)` + `DiscreteTopology (dualZLattice L)` — from
  `dualZLattice_eq_span` + `instIsZLatticeRealSpan` (transport across the proved carrier
  equality; both are `Prop`-classes).
* the **covolume reciprocal** `covolume (dualZLattice L) * covolume L = 1` — via
  `dualZLattice_eq_span` + `ZLattice.covolume_eq_det` and the fact that the dual-basis matrix is
  `(Bᵀ)⁻¹` (so its determinant is `(det B)⁻¹`).

See `.mathlib-quality/substrate-api.md` for the verified mathlib footholds.
-/

namespace DedekindResidue

@[expose] public section

open LinearMap.BilinForm MeasureTheory Matrix
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The inner-product bilinear form `innerₗ V` of a real inner product space is nondegenerate:
if `⟪x, ·⟫ ≡ 0` then `x = 0` (and symmetrically). Both separating conditions reduce, by
symmetry, to `⟪x, x⟫ = 0 → x = 0`. -/
theorem innerₗ_nondegenerate : Nondegenerate (innerₗ V) :=
  ⟨fun x hx => inner_self_eq_zero.mp (by have h := hx x; rwa [innerₗ_apply_apply] at h),
   fun x hx => inner_self_eq_zero.mp (by have h := hx x; rwa [innerₗ_apply_apply] at h)⟩

/-- The **dual lattice** `L♯` of `L` in a finite-dimensional real inner product space:
`L♯ = {y | ∀ x ∈ L, ⟪y, x⟫ ∈ ℤ}`, built from the inner-product bilinear form. -/
noncomputable def dualZLattice (L : Submodule ℤ V) : Submodule ℤ V :=
  dualSubmodule (innerₗ V) L

                               
                                                                                           
                 
                                                      
                                                                       
         

                                                                                              
                                                                                              
                                                                                                   
theorem dualZLattice_eq_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (b : Module.Basis ι ℤ L) :
    dualZLattice L =
      Submodule.span ℤ (Set.range (dualBasis (innerₗ V) innerₗ_nondegenerate
        (b.ofZLatticeBasis ℝ))) := by
  unfold dualZLattice
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate (b.ofZLatticeBasis ℝ)

/-- The dual of a ℤ-lattice is discrete: it is the span of the dual basis' range. -/
instance instDiscreteTopologyDualZLattice (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] : DiscreteTopology (dualZLattice L) := by
  classical
  have := ZLattice.module_finite ℝ L
  have := ZLattice.module_free ℝ L
  rw [dualZLattice_eq_span L (Module.Free.chooseBasis ℤ L)]
  infer_instance

/-- The dual of a ℤ-lattice is again a ℤ-lattice: the dual basis spans `V` over `ℝ`. -/
instance instIsZLatticeDualZLattice (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (dualZLattice L) where
  span_top := by
    classical
    have := ZLattice.module_finite ℝ L
    have := ZLattice.module_free ℝ L
    rw [dualZLattice_eq_span L (Module.Free.chooseBasis ℤ L)]
    exact ZSpan.span_top _

                                                                                        
                                                                        
                                                     
                                                                                              
                                                                                     
                                                                                       
                       

                                                                                    
                                                                                         
                                                                                                 
                                                         
                                                                                  
                                                                      
           
                                    
                                  
                                                                                      
                                                                                             
                                
                                                                               
                                                
                                                                              
                                                                                         
                                              
                                                                                
                                                                                          
                                                           
                                                                                     
                                  
                                                                          
                                                    
                                                                                                
                                                     
                                                                              
                                                    
                                                 
                                                            
                                                                  
                                                                              
                                                                    
                                                                 
                                                                                    
                                                                                           
                                                                              
           
                                           
                                          
                                                                         
                                                   
                                                                                
                                                            
                                                      
                                                                 
                                                       
                                                                                              
                                                                                   
                                                                                   

                                                                                        
                                    
                                                                                          
                                                              
                                                                  
                                         
                
                                                                                  
                                                                           
                                                                 
                                                    
                                                                                 
                                                                                   
                                         

                                                                                 
                                                                                         
                              
                                                                                              
                                         
                                                       
                                                               
                                                                              
                                          
           
                                    
                                  
                                                                                      
                                                                                             
                                
                                                                               
                                                                 
                                                               
                                                  
                                 
                                                                                            
            
                                                                              
                                                
       
                                                                                          
                                                                                       
                                                                     
                                   

end

end DedekindResidue
