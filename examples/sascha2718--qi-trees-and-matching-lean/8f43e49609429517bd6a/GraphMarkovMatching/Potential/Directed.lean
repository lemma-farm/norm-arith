module

/-
Directed potentials for two probability laws and a compatibility relation.
Two changes against the `Phi` of the support layer:

* **Directed**: the row law `μ` and the column law `ν` are different PMFs;
  the bad degree of a row point is measured against the column law. The
  support layer's `Phi α μ R` is the diagonal case `ν = μ`.
* **Safe at `q = 1`**: without reflexivity-on-support there is no guarantee
  that bad degrees stay below one, and `Real.rpow`'s junk value `0 ^ (-α) = 0`
  would silently zero out exactly the points that must contribute the most. The
  `ℝ≥0∞`-valued weight `phiE` is `⊤` at `q ≥ 1`, so finite potentials really
  do force `q < 1` wherever the row law charges, and the failure bound
  `𝔼 q ≤ Φ` holds unconditionally.

The `badInd` normal form `q_ν(z) = ∑' y, ν y · 𝟙[z ⋡ y]` makes the bad degree
linear in the column law, which is how the kernel mixture enters the step.
-/
public import GraphMarkovMatching.Process.Sim
public import GraphMarkovMatching.Support.Potential

@[expose] public section

namespace GraphMarkovMatching

open GraphMarkovMatching.Support
open scoped ENNReal Classical

universe u
variable {X : Type u}

/-! ### The safe weight `phiE` -/

/-- The `ℝ≥0∞`-valued potential weight: `φ_α` below `1`, `⊤` from `1` on. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

lemma phiE_of_lt {α t : ℝ} (h : t < 1) : phiE α t = ENNReal.ofReal (phi α t) :=
  ite_eq_left h

@[simp] lemma phiE_one (α : ℝ) : phiE α 1 = ⊤ := ite_eq_right (lt_irrefl 1)

                                                    
                                                      
      

                                                                           
                                                                                    
                            
                                                          
                                              
                                            
                                            
                                               

                                                                             
                                                                       
                              
                       
                                                            
                                                           
                                              
          
                

                                                                  
lemma ofReal_le_phiE {α t : ℝ} (hα : 0 ≤ α) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ENNReal.ofReal t ≤ phiE α t := by
  rcases lt_or_eq_of_le h1 with h | h
  · rw [phiE_of_lt h]
    exact ENNReal.ofReal_le_ofReal (le_phi hα h0 h)
  · rw [h, phiE_one]
    exact le_top

/-! ### The bad-degree normal form -/

/-- The bad indicator `𝟙[¬ R z y]` as an `ℝ≥0∞` weight. -/
noncomputable def badInd (R : X → X → Prop) (z y : X) : ℝ≥0∞ :=
  if R z y then 0 else 1

/-- `q_ν(z) = 𝔼_ν 𝟙[z ⋡ ·]`: the bad degree in the linear normal form. -/
lemma qE_eq_tsum_mul (ν : PMF X) (R : X → X → Prop) (z : X) :
    qE ν R z = ∑' y, ν y * badInd R z y := by
  rw [qE]
  exact tsum_congr fun y => by by_cases h : R z y <;> simp [badInd, h]

                                                                
                                                                                   
                                                      
                                    
                                                  

                                                     
                                                                              
                                                         
                                   

                                 

                                                                             
                     
                                                                         
                              

                                                               
                                                                     
                                    
                                                              
                          
                                        

                                          
                                                                
                                    
                                                                 
                         

                                                                        
                                                                       
                                                                             
                                             
           
                                         
                                                     
                                           
         
                                                                


                                                                                                 

end GraphMarkovMatching
