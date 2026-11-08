module

/-
Good and bad degrees for the two possible pairings of two independent coordinates.
-/
public import GraphMarkovMatching.Potential.Degrees
public import GraphMarkovMatching.Potential.Inverse
public import GraphMarkovMatching.Support.Contraction

@[expose] public section

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

lemma rE_square_two (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
        + aOverlap ν₀ R x₀ x₁ * aOverlap ν₁ R x₀ x₁
      = rE ν₀ R x₀ * rE ν₁ R x₁ + rE ν₁ R x₀ * rE ν₀ R x₁ := by
  have hSq : (∑' p : X × X, if SquareRel R (x₀, x₁) p then ν₀ p.1 * ν₁ p.2 else 0)
      = rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁) := by
    rw [rE]; simp_rw [prodPMF_apply]
  have hInt : (∑' p : X × X,
        if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then ν₀ p.1 * ν₁ p.2 else 0)
      = aOverlap ν₀ R x₀ x₁ * aOverlap ν₁ R x₀ x₁ := by
    rw [show aOverlap ν₀ R x₀ x₁ = ∑' y, if R x₀ y ∧ R x₁ y then ν₀ y else 0 from rfl,
      show aOverlap ν₁ R x₀ x₁ = ∑' y, if R x₀ y ∧ R x₁ y then ν₁ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then ν₀ p.1 * ν₁ p.2 else 0)
          = (if R x₀ p.1 ∧ R x₁ p.1 then ν₀ p.1 else 0)
            * (if R x₀ p.2 ∧ R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases h00 : R x₀ p.1 <;> by_cases h01 : R x₀ p.2 <;>
             by_cases h10 : R x₁ p.1 <;> by_cases h11 : R x₁ p.2 <;>
             simp [h00, h01, h10, h11]]
    exact tsum_prod_split (fun y => if R x₀ y ∧ R x₁ y then ν₀ y else 0)
      (fun y => if R x₀ y ∧ R x₁ y then ν₁ y else 0)
  have hA : (∑' p : X × X, if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = rE ν₀ R x₀ * rE ν₁ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if R x₀ p.1 then ν₀ p.1 else 0) * (if R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    exact tsum_prod_split (fun y => if R x₀ y then ν₀ y else 0)
      (fun y => if R x₁ y then ν₁ y else 0)
  have hB : (∑' p : X × X, if R x₁ p.1 ∧ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = rE ν₁ R x₀ * rE ν₀ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if R x₁ p.1 ∧ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if R x₁ p.1 then ν₀ p.1 else 0) * (if R x₀ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₁ p.1 <;> by_cases hb : R x₀ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if R x₁ y then ν₀ y else 0)
      (fun y => if R x₀ y then ν₁ y else 0)]
    rw [show (∑' y, if R x₁ y then ν₀ y else 0) = rE ν₀ R x₁ from rfl,
      show (∑' y, if R x₀ y then ν₁ y else 0) = rE ν₁ R x₀ from rfl]
    ring
  have hadd : (∑' p : X × X, if SquareRel R (x₀, x₁) p then ν₀ p.1 * ν₁ p.2 else 0)
        + (∑' p : X × X,
            if (R x₀ p.1 ∧ R x₁ p.1) ∧ (R x₀ p.2 ∧ R x₁ p.2) then ν₀ p.1 * ν₁ p.2 else 0)
      = (∑' p : X × X, if R x₀ p.1 ∧ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
        + (∑' p : X × X, if R x₁ p.1 ∧ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0) := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun p => ?_
    by_cases h00 : R x₀ p.1 <;> by_cases h01 : R x₀ p.2 <;>
      by_cases h10 : R x₁ p.1 <;> by_cases h11 : R x₁ p.2 <;>
      simp [SquareRel, h00, h01, h10, h11]
  rw [hSq, hInt, hA, hB] at hadd
  exact hadd

lemma qE_square_two (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    qE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
      ≤ qE ν₀ R x₀ * qE ν₁ R x₀ + qE ν₀ R x₁ * qE ν₁ R x₁
        + cOverlap ν₀ R x₀ x₁ + cOverlap ν₁ R x₀ x₁ := by
  have hq : qE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)
      = ∑' p : X × X, if SquareRel R (x₀, x₁) p then 0 else ν₀ p.1 * ν₁ p.2 := by
    rw [qE]; simp_rw [prodPMF_apply]
  have hpoint : ∀ p : X × X,
      (if SquareRel R (x₀, x₁) p then 0 else ν₀ p.1 * ν₁ p.2)
        ≤ (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
          + (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0) := by
    intro p
    by_cases hsq : SquareRel R (x₀, x₁) p
    · rw [ite_eq_left hsq]; exact zero_le
    · rw [ite_eq_right hsq]
      have hcov : (¬ R x₀ p.1 ∧ ¬ R x₀ p.2) ∨ (¬ R x₁ p.1 ∧ ¬ R x₁ p.2)
                ∨ (¬ R x₀ p.1 ∧ ¬ R x₁ p.1) ∨ (¬ R x₀ p.2 ∧ ¬ R x₁ p.2) := by
        by_contra hc
        exact hsq (by show (R x₀ p.1 ∧ R x₁ p.2) ∨ (R x₀ p.2 ∧ R x₁ p.1); tauto)
      set w := ν₀ p.1 * ν₁ p.2
      set t0 := (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then w else 0)
      set t1 := (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then w else 0)
      set t2 := (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then w else 0)
      set t3 := (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then w else 0)
      rcases hcov with h | h | h | h
      · calc w = t0 := (ite_eq_left h).symm
          _ ≤ t0 + t1 := le_self_add
          _ ≤ t0 + t1 + t2 := le_self_add
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t1 := (ite_eq_left h).symm
          _ ≤ t0 + t1 := le_add_self
          _ ≤ t0 + t1 + t2 := le_self_add
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t2 := (ite_eq_left h).symm
          _ ≤ t0 + t1 + t2 := le_add_self
          _ ≤ t0 + t1 + t2 + t3 := le_self_add
      · calc w = t3 := (ite_eq_left h).symm
          _ ≤ t0 + t1 + t2 + t3 := le_add_self
  have h0 : (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = qE ν₀ R x₀ * qE ν₁ R x₀ := by
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if ¬ R x₀ p.1 then ν₀ p.1 else 0) * (if ¬ R x₀ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₀ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₀ y then ν₀ y else 0)
      (fun y => if ¬ R x₀ y then ν₁ y else 0)]
    congr 1 <;> · rw [qE]; exact tsum_congr fun y => by by_cases h : R x₀ y <;> simp [h]
  have h1 : (∑' p : X × X, if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = qE ν₀ R x₁ * qE ν₁ R x₁ := by
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if ¬ R x₁ p.1 then ν₀ p.1 else 0) * (if ¬ R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₁ p.1 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₁ y then ν₀ y else 0)
      (fun y => if ¬ R x₁ y then ν₁ y else 0)]
    congr 1 <;> · rw [qE]; exact tsum_congr fun y => by by_cases h : R x₁ y <;> simp [h]
  have h2 : (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
      = cOverlap ν₀ R x₀ x₁ := by
    rw [show cOverlap ν₀ R x₀ x₁ = ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then ν₀ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
          = (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 else 0) * ν₁ p.2
        by by_cases ha : R x₀ p.1 <;> by_cases hb : R x₁ p.1 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => if ¬ R x₀ y ∧ ¬ R x₁ y then ν₀ y else 0) (fun y => ν₁ y),
      PMF.tsum_coe, mul_one]
  have h3 : (∑' p : X × X, if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
      = cOverlap ν₁ R x₀ x₁ := by
    rw [show cOverlap ν₁ R x₀ x₁ = ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then ν₁ y else 0 from rfl]
    rw [tsum_congr fun p : X × X => show
        (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          = ν₀ p.1 * (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₁ p.2 else 0)
        by by_cases ha : R x₀ p.2 <;> by_cases hb : R x₁ p.2 <;> simp [ha, hb]]
    rw [tsum_prod_split (fun y => ν₀ y) (fun y => if ¬ R x₀ y ∧ ¬ R x₁ y then ν₁ y else 0),
      PMF.tsum_coe, one_mul]
  rw [hq]
  calc ∑' p : X × X, (if SquareRel R (x₀, x₁) p then 0 else ν₀ p.1 * ν₁ p.2)
      ≤ ∑' p : X × X,
          ((if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
            + (if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
            + (if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
            + (if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)) :=
        ENNReal.tsum_le_tsum hpoint
    _ = (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₀ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₁ p.1 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₀ p.1 ∧ ¬ R x₁ p.1 then ν₀ p.1 * ν₁ p.2 else 0)
          + (∑' p : X × X, if ¬ R x₀ p.2 ∧ ¬ R x₁ p.2 then ν₀ p.1 * ν₁ p.2 else 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ = qE ν₀ R x₀ * qE ν₁ R x₀ + qE ν₀ R x₁ * qE ν₁ R x₁
          + cOverlap ν₀ R x₀ x₁ + cOverlap ν₁ R x₀ x₁ := by
        rw [h0, h1, h2, h3]

lemma rE_square_two_toReal (ν₀ ν₁ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    (rE (prodPMF ν₀ ν₁) (SquareRel R) (x₀, x₁)).toReal
        + (aOverlap ν₀ R x₀ x₁).toReal * (aOverlap ν₁ R x₀ x₁).toReal
      = (rE ν₀ R x₀).toReal * (rE ν₁ R x₁).toReal
        + (rE ν₁ R x₀).toReal * (rE ν₀ R x₁).toReal := by
  have h := rE_square_two ν₀ ν₁ R x₀ x₁
  apply_fun ENNReal.toReal at h
  rw [ENNReal.toReal_add rE_ne_top
      (ENNReal.mul_ne_top (aOverlap_ne_top ν₀ R x₀ x₁) (aOverlap_ne_top ν₁ R x₀ x₁)),
    ENNReal.toReal_add (ENNReal.mul_ne_top rE_ne_top rE_ne_top)
      (ENNReal.mul_ne_top rE_ne_top rE_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul] at h
  exact h

                                                                           
                                                      
                                                 
                                                   
                                                                           
                                       
                                                  
                                                   
                                                               
                                                          
                                                  
                                                                            
                                 
                                          
                                                
                                                                              
                                   
                                                                
                                   
                                         
                                                    
             

                                                                                
                     
                       
                   
                                          
             
                                    
                                    
                       
                          
                      
               
                                      
                                      
                                                                                   
                                                   
                      
                                                            
                                                                                           
                                                                                       
                                                                                       
                               
                                                               
                                                       
                                                       
                                                                 

                                                                            
                                                                             
                                                                              
                                     
                                        
                                                            
                                                                               
                                                                               
                                                               
                                           
                                                          
                                                                                   
                                     
                                         
                                  
                                                                               
                                      

section
variable {X : Type}

lemma straight_le_rE_square (ρc ρd : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE ρc R x₀ * rE ρd R x₁
      ≤ rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) := by
  rw [rE_eq_tsum_mul ρc R x₀, rE_eq_tsum_mul ρd R x₁,
    rE_eq_tsum_mul (prodPMF ρc ρd) (SquareRel R) (x₀, x₁),
    ← tsum_prod_split (fun y => ρc y * goodInd R x₀ y)
      (fun y => ρd y * goodInd R x₁ y)]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases h0 : R x₀ p.1 <;> by_cases h1 : R x₁ p.2
  · have hsq : SquareRel R (x₀, x₁) p := Or.inl ⟨h0, h1⟩
    simp [goodInd, h0, h1, hsq, prodPMF_apply]
  · simp [goodInd, h1]
  · simp [goodInd, h0]
  · simp [goodInd, h0]

lemma crossed_le_rE_square (ρc ρd : PMF X) (R : X → X → Prop) (x₀ x₁ : X) :
    rE ρc R x₁ * rE ρd R x₀
      ≤ rE (prodPMF ρc ρd) (SquareRel R) (x₀, x₁) := by
  rw [rE_eq_tsum_mul ρc R x₁, rE_eq_tsum_mul ρd R x₀,
    rE_eq_tsum_mul (prodPMF ρc ρd) (SquareRel R) (x₀, x₁),
    ← tsum_prod_split (fun y => ρc y * goodInd R x₁ y)
      (fun y => ρd y * goodInd R x₀ y)]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases h0 : R x₀ p.2 <;> by_cases h1 : R x₁ p.1
  · have hsq : SquareRel R (x₀, x₁) p := Or.inr ⟨h0, h1⟩
    simp [goodInd, h0, h1, hsq, prodPMF_apply]
  · simp [goodInd, h1]
  · simp [goodInd, h0]
  · simp [goodInd, h0]

                                                                            
                                                   
                                                                     
             
            
                                                                          
                
                                                                             
                   
                                                        
                                                                 
                                                    
                                                     
                                                                      
                                            
                                                                    
                                 

                                                                   
                 
                                                   
                                        
                                            
                                          
                                                  
                                                      
       

                                                                  
                                  
                                                 
                                                     
                                                       
                                                                      
                                                
                                                          
                                                               
                                   
                                                                     
                                           
                                       
                                               
                                                    
                                              

                                                                          
                                  
                                                 
                                                     
                                                       
                                                                      
                                                
                                                          
                                                               
                                   
                                                                     
                                           
                                       
                                              
                                                    
                                              

end

end GraphMarkovMatching
