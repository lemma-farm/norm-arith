/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Duality
public import ArithmeticHeights.Extraction
public import ArithmeticHeights.MinkowskiSecond
public import ArithmeticHeights.MixedBall
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Bombieri–Vaaler over a number field: the Hermitian form

**Bombieri–Vaaler 1983; the inequality Vaaler 2003 quotes as (1.3).** Let `K` be a number field of
degree `d` with `r₁` real and `r₂` complex places and discriminant `D`, and let `V ⊆ Kⁱ` be a
subspace of dimension `k`. Then `V` has a basis `x₁, …, x_k` of vectors with coordinates in
`𝓞 K` and

```text
∏_{l} H_Ar(x l)  ≤  (2^k / ω_k)^{r₁} (2^k / ω_{2k})^{r₂} · |D|^{k/2} · H_Ar(V),
```

relative Arakelov heights on both sides, `ω_n` the volume of the unit ball of `ℝⁿ`; taking `d`-th
roots gives the absolute form the literature states. For `V` the solution space of `A x = 0` the
right-hand side is the Arakelov height of the **row space** of `A`, by the duality theorem of
Layer 3.5.

## Main results

* `NumberField.exists_basis_prod_arakelovMulHeight_le`: the displayed inequality.
* `NumberField.exists_basis_prod_arakelovMulHeight_rpow_le`: its absolute form, all heights raised
  to the power `1/d`.
* `NumberField.exists_basis_ker_prod_arakelovMulHeight_rpow_le`: the matrix form — a basis of the
  solution space of `A x = 0`, bounded by the Arakelov height of the row space of `A`.
* `NumberField.mixedEmbedding.arakelovMulHeight_le_of_mem_smul_mixedBall`: the height of an
  integral tuple lying in `λ · mixedBall` is at most `λ ^ d`.
* `NumberField.mixedEmbedding.prod_successiveMinimum_mixedBall_le`: Minkowski's second theorem for
  the ℓ² body, with the covolume of Layer 4.3 and the slice volume of `MixedBall.lean` inserted.

## Implementation notes

⚠ **The constant is `2^{d k}` from Layer 4.2 against `2^{−r₂ k}` from Layer 4.3, and what survives
is `2^{k(r₁ + r₂)}`.** Over `ℤ` the two powers of two cancelled exactly (Layer 5.2); here they do
not, because the unit balls of the ℓ² norms are not the unit cubes, and the residue
`(2^k/ω_k)^{r₁} (2^k/ω_{2k})^{r₂}` is exactly the ratio between a cube and a ball. Layer 5.4
replaces the balls by cubes and polydiscs, and that is where cube slicing is needed.

⚠ **The rank hypothesis of the milestone is unnecessary.** The matrix form is stated for an
arbitrary `A`: Layer 3.5's `Matrix.arakelovMulHeight_ker_mulVecLin` identifies the height of the
solution space with the height of the row space with no hypothesis on `A`, and the geometric half
never looks at `A` at all. Stating `LinearIndependent K A.row` would only fix `k = N − M`.

⚠ **`k = 0` needs no special case.** The empty product is `1`, and Minkowski's second theorem
applied to the zero-dimensional lattice gives `1 ≤ C · H_Ar(V)` directly; no value of `ω_0` is
ever needed. For the same reason the basis is built with `Basis.mk` and a rank count rather than
with `basisOfLinearIndependentOfCardEqFinrank`, which demands a nonempty index type.

⚠ **The extraction of Layer 4.4 is applied to `ℚ`-linearity, not `ℤ`-linearity.** The mixed
embedding is a `ℤ`-linear map, but the counting argument needs a map of `ℚ`-vector spaces;
`AddMonoidHom.toRatLinearMap` supplies it, since a `ℚ`-linear structure on an additive group is
unique.

## References

E. Bombieri and J. D. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), Theorem 9 and §I.

J. D. Vaaler, "The best constant in Siegel's lemma", *Monatshefte für Mathematik* **140** (2003),
71–89, (1.3).

W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations", *Annals of
Mathematics* **85** (1967), 430–472, §3, for the covolume identity this consumes.

This is Layer 5.3 of the `ArithmeticHeights` roadmap.
-/

public section

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix
open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
theorem sq_norm_realPart_mixedPiEmb (w : {w : InfinitePlace K // IsReal w}) (x : ι → K) :
    ‖realPart K ι w (mixedPiEmb K ι x)‖ ^ 2 = ∑ j, w.1 (x j) ^ 2 := by
  have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
    rw [mixedPiEmb_apply]
    exact (toMixedPi K ι).symm_apply_apply _
  rw [realPart_apply, EuclideanSpace.sq_norm_toLp, hs]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).1 w‖ := by
    rw [← normAtPlace_apply_of_isReal w.2, normAtPlace_apply]
  rw [hw, Real.norm_eq_abs, sq_abs]

open scoped Classical in
theorem sq_norm_complexPart_mixedPiEmb (w : {w : InfinitePlace K // IsComplex w}) (x : ι → K) :
    ‖complexPart K ι w (mixedPiEmb K ι x)‖ ^ 2 = ∑ j, w.1 (x j) ^ 2 := by
  have hs : (toMixedPi K ι).symm (mixedPiEmb K ι x) = fun l ↦ mixedEmbedding K (x l) := by
    rw [mixedPiEmb_apply]
    exact (toMixedPi K ι).symm_apply_apply _
  rw [complexPart_apply, EuclideanSpace.sq_norm_toLp_complex, hs]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hw : w.1 (x j) = ‖(mixedEmbedding K (x j)).2 w‖ := by
    rw [← normAtPlace_apply_of_isComplex w.2, normAtPlace_apply]
  rw [hw, Complex.sq_norm]

open scoped Classical in
theorem sum_sq_le_of_mem_smul_mixedBall {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hmem : mixedPiEmb K ι x ∈ r • mixedBall K ι) (w : InfinitePlace K) :
    ∑ j, w (x j) ^ 2 ≤ r ^ 2 := by
  rw [mem_smul_mixedBall hr] at hmem
  rcases w.isReal_or_isComplex with h | h
  · have h1 := hmem.1 ⟨w, h⟩
    have h2 := sq_norm_realPart_mixedPiEmb (K := K) ⟨w, h⟩ x
    nlinarith [norm_nonneg (realPart K ι ⟨w, h⟩ (mixedPiEmb K ι x))]
  · have h1 := hmem.2 ⟨w, h⟩
    have h2 := sq_norm_complexPart_mixedPiEmb (K := K) ⟨w, h⟩ x
    nlinarith [norm_nonneg (complexPart K ι ⟨w, h⟩ (mixedPiEmb K ι x))]

open scoped Classical in
/-- **The height of an integral tuple in a dilate of the body.** -/
theorem arakelovMulHeight_le_of_mem_smul_mixedBall {r : ℝ} (hr : 0 < r) {x : ι → K}
    (hx : x ≠ 0) (hint : ∀ l, ∃ z : 𝓞 K, (z : K) = x l)
    (hmem : mixedPiEmb K ι x ∈ r • mixedBall K ι) :
    arakelovMulHeight x ≤ r ^ finrank ℚ K := by
  rw [arakelovMulHeight_eq hx]
  have hpow : ∀ n : ℕ, ((r ^ 2 : ℝ)) ^ ((n : ℝ) / 2) = r ^ n := by
    intro n
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r n]
    congr 1
    push_cast
    ring
  have harch : (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
      ≤ r ^ finrank ℚ K := by
    calc (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
        ≤ ∏ w : InfinitePlace K, r ^ w.mult := by
          refine Finset.prod_le_prod₀ (fun w _ ↦ Real.rpow_nonneg (by positivity) _)
            fun w _ ↦ ?_
          rw [← hpow w.mult]
          exact Real.rpow_le_rpow (by positivity)
            (sum_sq_le_of_mem_smul_mixedBall hr hmem w) (by positivity)
      _ = r ^ (∑ w : InfinitePlace K, w.mult) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = r ^ finrank ℚ K := by rw [InfinitePlace.sum_mult_eq]
  have hfin := finprod_finitePlace_le_one hx hint
  have hfin0 : 0 ≤ ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun i ↦ apply_nonneg _ _
  have harch0 : 0 ≤ ∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ) :=
    Finset.prod_nonneg fun w _ ↦ Real.rpow_nonneg (by positivity) _
  calc (∏ w : InfinitePlace K, (∑ i, w (x i) ^ 2) ^ (w.mult / 2 : ℝ))
        * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)
      ≤ (r ^ finrank ℚ K) * 1 := mul_le_mul harch hfin hfin0 (by positivity)
    _ = r ^ finrank ℚ K := mul_one _

section Span

                                                  

                       
                        
                                   
                                                                              
                                                        

                       
                        
                                                     
                                                                             
                                                                           
                                  

                       
                        
                                     
                                                                              
                                                    

                       
                        
                                      
                                                                                            
                   
                                                                                               
                                               
                           
                 
                                     
         

                       
                        
                                              
                                                                                            
                
                                
                                                                 
                                                                                     
                               

                        
                                                                          
                                             
                                                    
                                                 
                                                                           
                                                                               
                                                                                          
                                                                                             
                                                                                    
                                                                              
                                                                             
                                   
                                                                                            
                                                     
                                                                    
                                                                                    
                                                                          
                                                      
                                                     
                                                                  
                                                                  
                                               
                                                   
              
                                                             
                                                                 
                                                                                                 
                                 
                                                                             
                                      
                                                                                           
                                                      
                                                                 
                                           
                                                                 
                                           
                                                       
                       
              
                                                                   
                                                                   
                                                        
         
                                                                
                                              

end Span

end NumberField.mixedEmbedding

namespace NumberField

                                                                      
                               
                     

                                                                      

section Main

                                                  

                        
                                        
                                                
                                                              
                                    
                                    
                                                                                 
                                                                                            
                                                                                               
                                                                                                  
                                           
                                                                            
                                                      
                                             
                                           
                                  
                                                                                                 
              
                                                                                      
                                                                                             
           
                                                                                          
                                                  
                                  
                                                                                               
                                                 
                                                                               
                                                                        
                                                             
                                                             
                                                          
                            
                                                                                          
                                            
                                                                          
                                                    
                                                                             
                                                                                                
                                    
           
                                                            
                            
                                                                                    
                                                                                 
                    
                                                                                       
                                                           
                                                 
                           
                                          
                                         
                                                                                   
           
                                                                  
                                                                 
                                          
                                                                                
                                              
                              
                                                         
                                                     
                                                                            
                                                                                             
                                                                                      
                                           
                                                                           
                                                                                         
                                                                                
                                                                                   
                                                                
                                                                
                                                  

                        
                                        
                                                     
                                                              
                                    
                                                          
                                                                                  
                                                                                               
                                   
                                                                                 
                                                           
                                                                         
                            
                                                                                    
                                              
                                                  
                                       
                                                                   
                                                               
                                                                       
            
                                                                                             
                                                       
                                  
                                                                                         
                                                                                   
                          
                                                                                    
                                                                     
           
              
                                                    
                                                  
                                                      
      

end Main

section Kernel

                                

                        
                                                                           
                                                                                        
                                                      
                                                       
                                               
                                                                                
                                                          
                                                                                               
                                                                       
                                                                                              
          
                                
                                                                           
                                                    
                                                      
                                                                                             
                                                                      
                             
                                                                                   
                                            
                                                     
                                                     
             
                     
                                                                  
                                                                                              
             
                                                                 
             

end Kernel

end NumberField
