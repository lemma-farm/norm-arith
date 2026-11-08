/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Hadamard
public import ArithmeticHeights.MinimaBasis
public import ArithmeticHeights.MinkowskiSecond
public import ArithmeticHeights.UnitTorsion
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# The regulator and the heights of a fundamental system

Let `K` be a number field of degree `d = [K : ℚ]` and unit rank `r`, and write `h` for the
absolute logarithmic height. This file compares the regulator of `K` with the heights of a
fundamental system of units, in both directions:

```text
regulator K ≤ (2 d) ^ r * ∏ i, h (ε i)                for every fundamental system ε,
∏ i, h (ε i) ≤ (r !) ^ 2 / (2 ^ (r - 1) * d ^ r) * R  for some fundamental system ε.
```

The first is **Hadamard's inequality**. The regulator is the absolute determinant of the `r × r`
matrix of the logarithmic embeddings of the system (Mathlib's
`NumberField.Units.regOfFamily_eq_det'`); each row of that matrix has ℓ¹ norm at most
`2 d h (ε i)` by Layer 6.1; and the determinant of a square matrix is at most the product of the
ℓ¹ norms of its rows, which is Layer 3.4 in the square form `Matrix.abs_det_le_prod_sum_abs`.

The second is **Bugeaud–Győry's Lemma 1** in the case `S = S∞`, and it is where both halves of
Layer 4 are spent. Minkowski's second theorem (4.2) for `NumberField.Units.unitLattice K`, whose
covolume is the regulator, against the closed ℓ¹ unit ball of the log space, whose volume is
`2 ^ r / r !`, gives `∏ i, λ i ≤ r ! * R`; the basis of Layer 4.6 realizes the `i`-th minimum up
to `max 1 ((i + 1) / 2)` and so costs `r ! / 2 ^ (r - 1)`; and Layer 6.1 turns the ℓ¹ norm of a
lattice vector back into a height, which costs `d ^ (-r)`.

## Main results

* `NumberField.Units.regulator_le_prod_absLogHeight₁`: **Hadamard's bound**, for Mathlib's
  `fundSystem`; `NumberField.Units.regOfFamily_le_prod_absLogHeight₁` is the same bound for an
  arbitrary family and its own regulator, and
  `NumberField.Units.regulator_le_prod_absLogHeight₁_of_closure_sup_torsion_eq_top` for an
  arbitrary fundamental system. `NumberField.Units.regulator_le_prod_logHeight₁` is the relative
  form, where the constant is `2 ^ r`.
* `NumberField.Units.exists_fundSystem_prod_absLogHeight₁_le`: **a fundamental system of small
  height exists**, with the explicit constant `(r !) ^ 2 / (2 ^ (r - 1) d ^ r)`, and
  `NumberField.Units.exists_fundSystem_regulator_le_and_prod_absLogHeight₁_le` says that one and
  the same system satisfies both bounds.
* `NumberField.Units.logBall`: the closed ℓ¹ unit ball of the log space, with
  `NumberField.Units.volume_logBall` its volume `2 ^ r / r !` and
  `NumberField.Units.prod_successiveMinimum_logBall_le` Minkowski's second theorem against it.
* `NumberField.Units.closure_sup_torsion_eq_top_of_span`: a family of units whose logarithmic
  embeddings span the unit lattice over `ℤ` is a fundamental system, and
  `NumberField.Units.regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top`: a fundamental system
  has the regulator of the field for its own regulator.
* `NumberField.Units.prod_absLogHeight₁_pos_of_closure_sup_torsion_eq_top`: no member of a
  fundamental system is a root of unity, so both bounds are bounds between positive numbers.
* `NumberField.Units.regulator_eq_one_of_rank_eq_zero`: at unit rank zero the two bounds meet and
  the regulator is `1`.

## Implementation notes

⚠ **The second statement is an existence statement and cannot be made for `fundSystem`, or for
every fundamental system.** A unimodular change of basis multiplies the heights without touching
the regulator, so no bound in the direction `∏ h (ε i) ≤ c R` can hold uniformly. The family
produced here is built from the successive minima and has nothing to do with Mathlib's
`fundSystem`. What makes it a *fundamental system* rather than merely a family of maximal rank is
that the basis of Layer 4.6 is a basis of the whole unit lattice;
`closure_sup_torsion_eq_top_of_span` is the step that turns that into
`Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤`, through the kernel of `logEmbedding`. Nor is it
a statement with unspecified constants: for a fixed `K`,
`∃ c₁ c₂ > 0, c₁ R ≤ ∏ h (ε i) ≤ c₂ R` is true of any positive numbers and says nothing.

⚠ **Hadamard's inequality is used in the ℓ¹ form, not the familiar ℓ² one.** Layer 3.4 bounds the
Gram determinant `det (A Aᵀ)` by the product of the squared ℓ² norms of the rows, and extracting a
square root of that would need `Real.sqrt`. What Layer 6.1 hands over is the **ℓ¹** norm of a row,
so the ℓ² route would pay a factor `√r` per row and then have to give it back. The square form
added to Layer 3.4 for this layer, `Matrix.abs_det_le_prod_sum_abs`, stays inside the ordered field
and needs no analysis. ⚠ The `2 d` and not `d` in the constant is Layer 6.1's factor `2` — the
price of the coordinate that `logEmbedding` drops — and not a loss in Hadamard's inequality.

⚠ **Unit rank zero is not a degenerate case to be discarded; it is where the two bounds meet.**
Mathlib's `MeasureTheory.volume_sum_rpow_le` wants a nonempty index, so `volume_logBall` does
`r = 0` by hand: the log space is a single point, the ball is all of it, and its volume is
`1 = 2 ^ 0 / 0 !`. Both bounds then read `R ≤ 1` and `1 ≤ R`, and `regulator_eq_one_of_rank_eq_zero`
falls out — a value Mathlib does not record, having only `NumberField.Units.regulator_pos`. The
truncated subtraction in `2 ^ (r - 1)` is what the constant wants: it is `1` at `r = 0` and at
`r = 1`, and `∏_{i < r} max 1 ((i + 1) / 2) = r ! / 2 ^ (r - 1)` on the nose.

⚠ **That the bounds are not vacuous comes from two different places.** Layer 6.2 puts every member
of Mathlib's `fundSystem` strictly above height one, because its logarithmic embedding is a basis
vector of the unit lattice. For an *arbitrary* fundamental system that argument is not available,
and the positivity instead comes from this layer: such a family has maximal rank, because its
regulator is the regulator of `K` and that is nonzero, and a linearly independent family has no
zero member. The acceptance criteria also check that the two constants are mutually consistent,
`1 ≤ (2 d) ^ r * (r !) ^ 2 / (2 ^ (r - 1) d ^ r)`, which the two bounds and the positivity of the
regulator force.

## References

Y. Bugeaud and K. Győry, "Bounds for the solutions of unit equations", *Acta Arithmetica* **74**
(1996), 67–80; Lemma 1 of §3 (p. 71) is the second statement, for `S`-units, and its proof on
pp. 71–72 is the route taken here. Their `h` is the multiplicative absolute height, so their
`log h` is the `absLogHeight₁` of this file.

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter V,
Lemma 8 (p. 135), which is Layer 4.6, and Chapter VIII, Theorem V, which is Layer 4.2.

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5, where the comparison between the height of a unit and its logarithmic embedding is
Proposition 1.5.12.

This is Layer 6.3 of the `ArithmeticHeights` roadmap.
-/

public section

open Height Module NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem Real

open scoped Pointwise

namespace NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-!
### The ℓ¹ unit ball of the log space
-/

open scoped Classical in
/-- The closed ℓ¹ unit ball of `NumberField.Units.dirichletUnitTheorem.logSpace K`, the convex
body Minkowski's second theorem is applied to. -/
def logBall (K : Type*) [Field K] [NumberField K] : Set (logSpace K) :=
  {x | ∑ w, |x w| ≤ 1}

open scoped Classical in
theorem mem_logBall {x : logSpace K} : x ∈ logBall K ↔ ∑ w, |x w| ≤ 1 := Iff.rfl

open scoped Classical in
theorem convex_logBall : Convex ℝ (logBall K) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_logBall] at hx hy ⊢
  have hstep : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(a • x + b • y) w| ≤ a * |x w| + b * |y w| := fun w ↦ by
    simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x w) (b * y w)
  calc ∑ w, |(a • x + b • y) w| ≤ ∑ w, (a * |x w| + b * |y w|) :=
        Finset.sum_le_sum fun w _ ↦ hstep w
    _ = a * ∑ w, |x w| + b * ∑ w, |y w| := by rw [Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hab]

                        
                                                                                    
                              

                        
                                                     
                                                                        
                                          

                        
                                                                           
            
                        
                                             
                                                            
                       
                                                                                         
                                                

                        
                                                              
                                                              

                        
                                                                         
           
                                                               
                                                                          
              
                                               
                    
                                         
                                                                                             
                                        
                                                            
                                                        
                                                
                                                  
                                                               
                                                 
                                       
              
            
                                                                                               

                        
                                                                                                
                                            
                                                                            
                                                   
                           
                        
                                              
                           
                                                                                
                          
                      

                        
                                                          
                                                               
           
                                                                                

                        
                                                                                           
                                                                                                 
                                                                                                   
                                                              
                                    
                                                              
           
                                   
                                                                                                  
                                                                          
                              
                                                   
                    
                                           
           
                        
                                                                            
                                                             
          
                        
            
                                                                                               
           
                                       
               
                                                                                         
                   
                                                        

                        
                                                                                            
                                                                                                   
                                                                                                 
                                                                                 
                                 
                                                                 
                                              
           
                                                
                                         
                                                 
                                                                      
                                                                              
                                                                       
                                               
                                                        
                                                           
                                  
                
            

   
                             
  

                                                                                                 
                                                                                           
                                                              
                                              
                                                                                        
                  
                
                
                               
                                                                
           
                                            
              
              
                                                   
                                                                        
                                                                                
                                                   
                                              
                                   
               
             
                                                       
                

   
                       
  

                                                                                           
                                                                                               
                                                                                              
                            
                                                                       
                                                                                   
                          
                                                        
                           
         
                                                                
                                              
                                                         
                      
                                          
                                                
                                                              
                                
                                                                      
                                       
                                   
                                                                                   
                                   
                                                    
                                 
                                                                            
                                     
                                         
           
                                       

                                                                                      
                                                                                              
                                                                      
                                                                                          
                                                                                            
                                 
                                          
                                                  
                    
            

                                                                                                
            
                                                                           
                                                                         
                                  
                                                                                            

                                                                                             
                                                                                               
                                                                                              
                                
                                                                                
                                                                             
                               
                                                                         
                                     

                                                                                     
                                                                                   
                                                                             
                                          
                                                                                        

                                                                                               
                              
                                                                                        
                                                          
                                               
                                                                               

   
                    
  

                        
                                                                   
                                                                       
                                                    
                                                
           
                                 
                                                                                     
                                                                            
                                                                           
                                     
                                                               
             
                                                                 
                                                
                                                                                           
                                                            
                                    
                                                                       
                                                             
                                                                            
                                                                                        
                      
                   
                                                                             
                                                                                   
                                                                                           

                        
                                                                                                  
                                                                
                                                                               
                                                  
                                                           
                                          
                                                        

                        
                                                                
                                                                     
                                                                                      
                                                                                          
                                                                                                

                        
                                                                                           
                                                                                           
                                                                                                
                                                                         
                                                                    
                                                                        
                                    
                                                                   
                                                
                                                                               
                                                              
                                                                           
                                                 
                                                                                         
                                         
                                    
                                           

                        
                                                                          
                                                                            
                                                                                 
                                          
                                                     

   
                                        
  

                        
                                                                                             
             
                                                                                       
                                
                                                      
                                              
                                        
                                                                                 
           
                                                                                   
                                                                                            
            
                                                                                      
                                                                            
                                      
                                                              
                                                                                     
           
                                 
                                
                         
                                                          
                                                                 
                                                                          
                                                                                   
                              
                                                     
                                        
                                             
                                                                                          
             
                                                                                 
                                                                     
                                                                                            
                                                           
                                                                     
                                                                   
                                                                        
            
                
                                                     
                                                             
                                                                   
                                                                      
              
                                               
                                                                        
                                                                      
                                             
                                                                          
                                                                                   
                                   
                                                                      
                                                         
                                              
                                                                                
                                                                                      
                                                                                    
                                                                                         
                                                         
                                                                         
                                                            
                                                                                  
                                                                             
                                        
                                                                                         
                                                                      
                                                            
                
                                                        
                                               
                                                                             
                    

                        
                                                                                     
                                                                                                   
                                                                                                  
                                                                
                                           
                                
                                                      
                                                                                             
                                              
                                        
                                                                                 
                                                                    
                                                                                        

                        
                                                                                           
                                                                                               
                                                                                 
                                                                              
                                            
                                              
                                  
                                                   
                                                                                
                                         
                                                                     
                                                            
                     
               
          

   
                       
  

section Examples

                        
                                                                                              
                                                                                              
                                                               
                                                  
                                                        
                                                                          

                                                                                                   
                                                                                            
                                                                                              
                                                                    
                                                     
                                                                                                  

                        
                                                                                              
                                                                                                  
                                                  
                                                    
                                                                                          
                                                                                       
                            
                                                                     
                                              

end Examples

end NumberField.Units

end
