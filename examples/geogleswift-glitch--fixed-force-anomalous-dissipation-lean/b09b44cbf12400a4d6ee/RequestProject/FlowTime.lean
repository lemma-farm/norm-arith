module

public import RequestProject.FlowBasic

/-!
# Dependence of flow maps on the initial time

For a field which is Lipschitz in time, `Φ_{r → s}(z) = z + (s - r) V(s, z) + O((s - r)²)`
uniformly in `z`.  Consequently, along a differentiable curve `y`, the map
`r ↦ Φ_{r → s}(y r)` has derivative `y'(s) - V(s, y(s))` at `r = s`, and for the backward maps
`Y_r = Φ_{r → t₀}` the chain rule gives the transport equation `∂ᵣ (g ∘ Y_r) = -V · ∇(g ∘ Y_r)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real Asymptotics
open scoped NNReal

noncomputable section

namespace AnomDiss

namespace GoodField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {V : ℝ → E → E} {M K : ℝ≥0}

/-- Second-order expansion of a flow map in the initial time, uniformly in space. -/
lemma norm_gflow_sub_sub_smul_le (hV : GoodField V M K) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) (r s : ℝ) (z : E) :
    ‖gflow V r s z - z - (s - r) • V s z‖ ≤ (Lt + K * M) * (s - r) ^ 2 := by
  have hLt0 : 0 ≤ Lt := by
    have := hLt (r + 1) r z
    have h0 : (0:ℝ) ≤ Lt * |r + 1 - r| := (norm_nonneg _).trans this
    simpa using h0
  set H : ℝ → E := fun u => gflow V r u z - z - (u - r) • V s z with hH
  have hd : ∀ u, HasDerivAt H (V u (gflow V r u z) - V s z) u := by
    intro u
    have h1 := ((hasDerivAt_id u).sub_const r).smul_const (V s z)
    have := ((hV.hasDerivAt_gflow r u z).sub_const z).fun_sub h1
    simpa using this
  have hbd : ∀ u ∈ uIcc r s, ‖V u (gflow V r u z) - V s z‖ ≤ (Lt + K * M) * |s - r| := by
    intro u hu
    have hu1 : |u - s| ≤ |s - r| := by
      rcases le_total r s with h | h
      · rw [uIcc_of_le h] at hu
        rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonneg (by linarith)]; linarith [hu.1]
      · rw [uIcc_of_ge h] at hu
        rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonpos (by linarith)]; linarith [hu.2]
    have hu2 : |u - r| ≤ |s - r| := by
      rcases le_total r s with h | h
      · rw [uIcc_of_le h] at hu
        rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonneg (by linarith)]; linarith [hu.2]
      · rw [uIcc_of_ge h] at hu
        rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith)]; linarith [hu.1]
    have e1 := hLt u s (gflow V r u z)
    have e2 := (hV.lip s).dist_le_mul (gflow V r u z) z
    have e3 := hV.norm_gflow_sub_le r u z
    rw [dist_eq_norm, dist_eq_norm] at e2
    calc ‖V u (gflow V r u z) - V s z‖
        = ‖(V u (gflow V r u z) - V s (gflow V r u z)) + (V s (gflow V r u z) - V s z)‖ := by
          congr 1; abel
      _ ≤ Lt * |u - s| + K * (M * |u - r|) := by
          refine (norm_add_le _ _).trans (add_le_add e1 (e2.trans ?_))
          gcongr
      _ ≤ Lt * |s - r| + K * (M * |s - r|) := by gcongr
      _ = (Lt + K * M) * |s - r| := by ring
  have key := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) hbd left_mem_uIcc right_mem_uIcc
  have eH : H s - H r = gflow V r s z - z - (s - r) • V s z := by
    simp only [hH, hV.gflow_self, sub_self, zero_smul, sub_zero]
  rw [eH, Real.norm_eq_abs] at key
  calc _ ≤ (Lt + K * M) * |s - r| * |s - r| := key
    _ = _ := by rw [mul_assoc, ← sq, sq_abs]

                                                     
                                                              
                                                                                   
                              
                                                                    
                               
                                                                                    
                                                       
                                                                            
           
                      
                                  
        
               
                                                                              
                              
                                                                              
                                  
                                                                            
                                                                              
                                                                                    
                                               
                                                                 
                                              
                                                            
                                                         
                                                                       
                                                                             
                            
                                                      
                                                               
                                                             
                      
                                
                    

                                                                                 
                                                                
                                                                                         
                                                                       
                                                                                 
                                                
                                                                  
                                                                                                    
            
                                                   
        
                                              
                                                            
                 
                                            
                  

end GoodField

end AnomDiss
