-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantFields
public import RothschildStein.Definitions.SmoothDifferentialOperator.IsHomogeneous

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Left invariance on smooth functions (BB Definition 3.22(a), p. 106). -/
def IsLeftInvariantOperator (P : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → ∀ y,
    P (f ∘ G.mul y) = (P f) ∘ G.mul y

                                                                            
                                                                                
                                   
                                                               

                                                                       
def IsHomogeneousOperator (P : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ)
    (degree : ℝ) : Prop :=
  ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t, 0 < t → ∀ x,
    P (f ∘ G.dilate t) x = t ^ degree * P f (G.dilate t x)

/-- Smoothness preservation required when composing operators on the smooth-function domain. -/
def PreservesSmooth (P : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) (P f)

/-- Composition preserves left invariance (BB p. 107). -/
theorem IsLeftInvariantOperator.comp
    {P Q : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ}
    (hP : IsLeftInvariantOperator G P) (hQ : IsLeftInvariantOperator G Q)
    (hQs : PreservesSmooth Q) : IsLeftInvariantOperator G (P ∘ Q) := by
  intro f hf y
  change P (Q (f ∘ G.mul y)) = _
  rw [hQ f hf y, hP (Q f) (hQs f hf) y]
  rfl

/-- Composition adds homogeneity degrees (BB p. 107). -/
theorem IsHomogeneousOperator.comp
    {P Q : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ} {a b : ℝ}
    (hP : IsHomogeneousOperator G P a) (hQ : IsHomogeneousOperator G Q b)
    (hQs : PreservesSmooth Q) (hPl : ∀ c f, P (fun x => c * f x) = fun x => c * P f x) :
    IsHomogeneousOperator G (P ∘ Q) (a + b) := by
  intro f hf t ht x
  have he : Q (f ∘ G.dilate t) = fun x => t ^ b * (Q f ∘ G.dilate t) x :=
    funext (hQ f hf t ht)
  change P (Q (f ∘ G.dilate t)) x = _
  rw [he, hPl]
  dsimp only
  rw [hP (Q f) (hQs f hf) t ht x, Real.rpow_add ht]
  simp only [Function.comp_apply]
  ring

                                                                           
                                 
                                     
                                                                     
                                                       
              
          
                        
                                                                  
                                                                               
                                                  

                                                                             
                                 
                                      
                                                                      
                                                        
              
          
                        
                                                                  
                                                                                
                                                  

end RothschildStein.G2
