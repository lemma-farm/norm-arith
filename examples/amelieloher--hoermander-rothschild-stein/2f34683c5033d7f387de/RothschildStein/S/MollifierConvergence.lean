-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierKernel
public import RothschildStein.G2.MollifierLpConvergence
public import RothschildStein.G2.MollifierSmooth
public import RothschildStein.G2.MollifierUniform
public import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- The ordinary scaled real mollifier ε^{-n}J(x/ε)
(BB Lemma 2.8, p. 72). -/
def euclideanJScale (n : ℕ) (ε : ℝ) (x : Fin n → ℝ) : ℝ :=
  (ε^n)⁻¹ * euclideanJ n (ε⁻¹ • x)

/-- Ordinary zero-extended convolution by the scaled kernel
(BB Lemma 2.8, p. 72). -/
def euclideanRegularize (n : ℕ) (f : (Fin n → ℝ) → ℝ) (ε : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ z, euclideanJScale n ε (x-z) * f z

/-- The additive group kernel is exactly the ordinary scaled mollifier
(BB Lemma 2.8, p. 72; the Euclidean specialization). -/
theorem additiveMollifierScale_eq (hn : 0 < n) (ε : ℝ) :
    RothschildStein.G2.groupMollifierScale (additiveCoordinateGroup hn)
      (euclideanGroupMollifier hn) ε = euclideanJScale n ε := by
  funext x
  unfold RothschildStein.G2.groupMollifierScale euclideanJScale
  rw [additiveCoordinateGroup_dilate]
  have hd : (additiveCoordinateGroup hn).homogeneousDimension = n := by
    simp [HomogeneousGroup.homogeneousDimension,additiveCoordinateGroup]
  rw [hd]
  rfl

/-- The homogeneous-group regularizer specializes to ordinary Euclidean convolution (BB Lemma 2.8, p. 72). -/
theorem additiveRegularize_eq (hn : 0 < n) (f : (Fin n → ℝ) → ℝ) (ε : ℝ) :
    RothschildStein.G2.groupRegularize (additiveCoordinateGroup hn)
      (euclideanGroupMollifier hn) f ε = euclideanRegularize n f ε := by
  funext x
  unfold RothschildStein.G2.groupRegularize
  rw [RothschildStein.G2.groupConvolution_def,additiveMollifierScale_eq]
  simp only [additiveCoordinateGroup_mul,additiveCoordinateGroup_inv,← sub_eq_add_neg]
  rfl

                                                                                                
                                                                   
                                                                             
                                                                         
                          
                               
                                                                  
                                                              
                                                                 
                                                       
                                                                     

end RothschildStein.S
