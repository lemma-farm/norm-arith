import GraphMatrices.WalshFiniteL2
import GraphMatrices.MatrixAverageContraction
import GraphMatrices.FinitePaleyZygmund
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace GraphMatrices.Walsh

noncomputable section
open scoped BigOperators
open MatrixAverageContraction

variable {E : Type*} [Fintype E] [DecidableEq E]

def flipOne (x : E) : (E → Bool) ≃ (E → Bool) :=
  xorFlip (fun y => decide (y = x))

theorem sign_flipOne (x : E) (σ : E → Bool) :
    sign (flipOne x σ x) = - sign (σ x) := by
  change sign (Bool.xor (decide (x = x)) (σ x)) = -sign (σ x)
  cases σ x <;> norm_num [sign]

theorem character_flipOne_of_not_mem (x : E) (S : Finset E) (hx : x ∉ S)
    (σ : E → Bool) : character S (flipOne x σ) = character S σ := by
  rw [character_eq_prod, character_eq_prod]
  apply Finset.prod_congr rfl
  intro y hy
  have hyx : y ≠ x := by intro h; subst y; exact hx hy
  simp [flipOne, xorFlip, hyx]

theorem character_insert (x : E) (S : Finset E) (hx : x ∉ S) (σ : E → Bool) :
    character (insert x S) σ = sign (σ x) * character S σ := by
  simp [character_eq_prod, Finset.prod_insert hx]

def series (D : Finset E) (c : Finset E → ℝ) (σ : E → Bool) : ℝ :=
  polynomial D.powerset c σ

def weightedEnergy (D : Finset E) (c : Finset E → ℝ) : ℝ :=
  ∑ S ∈ D.powerset, (3 : ℝ)^S.card * (c S)^2

theorem weightedEnergy_nonneg (D : Finset E) (c : Finset E → ℝ) :
    0 ≤ weightedEnergy D c := by
  exact Finset.sum_nonneg (fun S _ => by positivity)

theorem series_flipOne (D : Finset E) (c : Finset E → ℝ)
    (x : E) (hx : x ∉ D) (σ : E → Bool) :
    series D c (flipOne x σ) = series D c σ := by
  apply Finset.sum_congr rfl
  intro S hS
  rw [character_flipOne_of_not_mem x S (fun h => hx (Finset.mem_powerset.mp hS h))]

theorem series_insert (D : Finset E) (c : Finset E → ℝ) (x : E) (hx : x ∉ D)
    (σ : E → Bool) :
    series (insert x D) c σ = series D c σ +
      sign (σ x) * series D (fun S => c (insert x S)) σ := by
  unfold series polynomial
  rw [Finset.sum_powerset_insert hx, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  rw [character_insert x S (fun h => hx (Finset.mem_powerset.mp hS h))]
  ring

theorem weightedEnergy_insert (D : Finset E) (c : Finset E → ℝ)
    (x : E) (hx : x ∉ D) :
    weightedEnergy (insert x D) c = weightedEnergy D c +
      3 * weightedEnergy D (fun S => c (insert x S)) := by
  unfold weightedEnergy
  rw [Finset.sum_powerset_insert hx, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.card_insert_of_notMem (fun h => hx (Finset.mem_powerset.mp hS h)), pow_succ]
  ring

theorem expect_sign_mul_eq_zero_of_flip (x : E) (f : (E → Bool) → ℝ)
    (hf : ∀ σ, f (flipOne x σ) = f σ) :
    independentSignLaw.expect (fun σ => sign (σ x) * f σ) = 0 := by
  have h := independent_expect_xorFlip (fun y => decide (y = x))
    (fun σ => sign (σ x) * f σ)
  change independentSignLaw.expect (fun σ => sign (flipOne x σ x) * f (flipOne x σ)) = _ at h
  simp_rw [sign_flipOne, hf, neg_mul] at h
  rw [FiniteLaw.expect_neg] at h
  linarith

theorem expect_fourth_split (D : Finset E) (c : Finset E → ℝ)
    (x : E) (hx : x ∉ D) :
    independentSignLaw.expect (fun σ => (series (insert x D) c σ)^4) =
      independentSignLaw.expect (fun σ => (series D c σ)^4) +
      6 * independentSignLaw.expect (fun σ =>
        (series D c σ)^2 * (series D (fun S => c (insert x S)) σ)^2) +
      independentSignLaw.expect (fun σ => (series D (fun S => c (insert x S)) σ)^4) := by
  let a := series D c
  let b := series D (fun S => c (insert x S))
  have hex (σ : E → Bool) :
      (series (insert x D) c σ)^4 = a σ^4 + 6*(a σ^2*b σ^2) + b σ^4 +
        sign (σ x) * (4*a σ^3*b σ + 4*a σ*b σ^3) := by
    rw [series_insert D c x hx]
    change (a σ + sign (σ x)*b σ)^4 = _
    cases h : σ x <;> simp only [sign, h, Bool.false_eq_true, ↓reduceIte] <;> ring
  have hz := expect_sign_mul_eq_zero_of_flip x
    (fun σ => 4*a σ^3*b σ + 4*a σ*b σ^3) (by
      intro σ
      dsimp [a,b]
      rw [series_flipOne D c x hx, series_flipOne D (fun S => c (insert x S)) x hx])
  rw [FiniteLaw.expect_congr independentSignLaw hex,
    FiniteLaw.expect_add, hz, add_zero, FiniteLaw.expect_add,
    FiniteLaw.expect_add, FiniteLaw.expect_smul]

/-- Finite Boolean hypercontractivity in its weighted coefficient form. -/
theorem fourth_le_weightedEnergy_sq (D : Finset E) (c : Finset E → ℝ) :
    independentSignLaw.expect (fun σ => (series D c σ)^4) ≤ (weightedEnergy D c)^2 := by
  induction D using Finset.induction_on generalizing c with
  | empty => simp [series, polynomial, character_empty, weightedEnergy, ← pow_mul]
  | @insert x D hx ih =>
    let a := series D c
    let b := series D (fun S => c (insert x S))
    let A := weightedEnergy D c
    let B := weightedEnergy D (fun S => c (insert x S))
    have hA : 0 ≤ A := weightedEnergy_nonneg _ _
    have hB : 0 ≤ B := weightedEnergy_nonneg _ _
    have ha : independentSignLaw.expect (fun σ => a σ^4) ≤ A^2 := ih c
    have hb : independentSignLaw.expect (fun σ => b σ^4) ≤ B^2 := ih _
    have hcross : independentSignLaw.expect (fun σ => a σ^2*b σ^2) ≤ A*B := by
      have hcs := FiniteLaw.expect_mul_sq_le independentSignLaw
        (fun σ => a σ^2) (fun σ => b σ^2)
      have h4 (z : ℝ) : (z^2)^2 = z^4 := by ring
      simp only [h4] at hcs
      have han : 0 ≤ independentSignLaw.expect (fun σ => a σ^4) :=
        FiniteLaw.expect_nonneg _ (fun _ => by positivity)
      have hbn : 0 ≤ independentSignLaw.expect (fun σ => b σ^4) :=
        FiniteLaw.expect_nonneg _ (fun _ => by positivity)
      have hp := mul_le_mul ha hb hbn (sq_nonneg A)
      have hAB := mul_nonneg hA hB
      nlinarith [sq_nonneg (independentSignLaw.expect (fun σ => a σ^2*b σ^2) - A*B)]
    rw [expect_fourth_split D c x hx, weightedEnergy_insert D c x hx]
    change independentSignLaw.expect (fun σ => a σ^4) +
      6*independentSignLaw.expect (fun σ => a σ^2*b σ^2) +
      independentSignLaw.expect (fun σ => b σ^4) ≤ (A+3*B)^2
    nlinarith [sq_nonneg B]

                                                         
                                                           
                                     
                                         
                                                                      

                                                                             
                                                   
                                                                                                
                                    
                         
            
                            
                                                                                         
                             

                                                                                            
                                                                           
                                                   
                                                           
                                                                                 
                                                 
                                       
      
                                                                 
                                                                                
                               
                                                                            

                                                             
                                                             
                                                               
                                                                                     
                                                            
                                                                            
                                                        
                                                   
                                
                
                   
                  
                   
                                                          
                 
                                                              
                   
                          

end
end GraphMatrices.Walsh
