module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.Affine
public import Mathlib
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Quantitative domain predicates

The compatibility boundedness predicate is retained alongside an explicit
Euclidean-diameter bound for quantitative Sobolev estimates.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

/-- Coordinatewise boundedness, compatible with the existing LIH API. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R

/-- The minimal measurable bounded domain class used by Sobolev integration. -/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U

/-- Every pair of points in `U` is at Euclidean distance at most `D`. -/
def HasEuclideanDiameterLE {d : ℕ}
    (U : Set (Vec d)) (D : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
    vecEuclideanNorm (x - y) ≤ D

namespace IsSobolevRegularDomain

                                               
                                     
                      
      

                                                 
                                     
                        
      

end IsSobolevRegularDomain

namespace HasEuclideanDiameterLE

theorem mono {d : ℕ} {U V : Set (Vec d)} {D : ℝ}
    (hU : HasEuclideanDiameterLE U D) (hVU : V ⊆ U) :
    HasEuclideanDiameterLE V D := by
  intro x hx y hy
  exact hU (hVU hx) (hVU hy)

                                                                      
                                                
                                                                  
               
                                 
                      
                                                  
                                      
                                        

                                                                        
                                                      
                                                   
                                                         
                 
                               
                               
                                                        

                                                                              
                                                  
                         
                                                     
                                      
             
                               
                                                       
                  
                                                       
                  
                                               
                                           
           
                          

                                                                           
                       
theorem smul {d : ℕ} {U : Set (Vec d)} {D : ℝ}
    (hU : HasEuclideanDiameterLE U D) (r : ℝ) :
    HasEuclideanDiameterLE (r • U) (|r| * D) := by
  intro x hx y hy
  rcases Set.mem_smul_set.mp hx with ⟨x', hx', rfl⟩
  rcases Set.mem_smul_set.mp hy with ⟨y', hy', rfl⟩
  rw [← smul_sub, vecEuclideanNorm_smul]
  exact mul_le_mul_of_nonneg_left (hU hx' hy') (abs_nonneg r)

                                                                            
          
                                                
                                                              
                                                
                                               

                                                                        
                                       
                                                 
                            
                                            
                                      
             
                           
               
                                        
                                  
                                                                
                                           
           
                                

end HasEuclideanDiameterLE

end PDE
