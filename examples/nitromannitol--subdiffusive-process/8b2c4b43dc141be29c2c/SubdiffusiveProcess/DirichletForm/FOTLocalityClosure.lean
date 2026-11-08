module

public import SubdiffusiveProcess.DirichletForm.FOTProduct

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

namespace ClosedForm

theorem form_add_self_le (E : ClosedForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u + v) (u + v) ≤ 2 * E.form u u + 2 * E.form v v := by
  have h := E.form_nonneg (u - v) (E.domain.sub_mem hu hv)
  rw [E.form_sub_self hu hv] at h
  rw [E.form_add_self hu hv]
  linarith

theorem form_sub_self_le (E : ClosedForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u - v) (u - v) ≤ 2 * E.form u u + 2 * E.form v v := by
  have h := E.form_nonneg (u + v) (E.domain.add_mem hu hv)
  rw [E.form_add_self hu hv] at h
  rw [E.form_sub_self hu hv]
  linarith

theorem form_smul_self (E : ClosedForm m) (c : ℝ) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) : E.form (c • u) (c • u) = c ^ 2 * E.form u u := by
  rw [E.form_smul_left c u hu _ (E.domain.smul_mem c hu), E.form_smul_right c hu hu]
  ring

                                                                
                                                             
                                       
                                                                      
                                          
                                                                          
                        
                                                                
           
                                            
                                                               
                                                                     
                                 
                                                                                    
             
                                                    
                      
                                                             
                                          
            
               
                                                          
                                                                         
                              
              
               
          

end ClosedForm

/-- A coarse product bound, sufficient for passing locality through bounded-energy limits. -/
theorem exists_mul_mem_form_le (F : _root_.SubdiffusiveProcess.DirichletForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hv : v ∈ F.domain) {M : ℝ}
    (huM : ∀ᵐ x ∂m, |u x| ≤ M) (hvM : ∀ᵐ x ∂m, |v x| ≤ M) :
    ∃ w : Lp ℝ 2 m, w ∈ F.domain ∧
      ⇑w =ᵐ[m] (fun x => u x * v x) ∧
      F.form w w ≤ 8 * M ^ 2 * (F.form u u + F.form v v) := by
  let K : ℝ≥0 := ⟨2 * |M|, by positivity⟩
  have hK0 : sqClamp K 0 = 0 := sqClamp_zero K.coe_nonneg
  let A := (lipschitzWith_sqClamp K).compLp hK0 (u + v)
  let B := (lipschitzWith_sqClamp K).compLp hK0 (u - v)
  have hAe : ⇑A =ᵐ[m] fun x => sqClamp K ((u + v : Lp ℝ 2 m) x) :=
    LipschitzWith.coeFn_compLp _ _ _
  have hBe : ⇑B =ᵐ[m] fun x => sqClamp K ((u - v : Lp ℝ 2 m) x) :=
    LipschitzWith.coeFn_compLp _ _ _
  have hA := lipschitz_comp_mem F (lipschitzWith_sqClamp K) hK0
    (F.domain.add_mem hu hv) hAe
  have hB := lipschitz_comp_mem F (lipschitzWith_sqClamp K) hK0
    (F.domain.sub_mem hu hv) hBe
  let w : Lp ℝ 2 m := (1 / 4 : ℝ) • (A - B)
  refine ⟨w, F.domain.smul_mem _ (F.domain.sub_mem hA.1 hB.1), ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul (1 / 4 : ℝ) (A - B), Lp.coeFn_sub A B,
      hAe, hBe, Lp.coeFn_add u v, Lp.coeFn_sub u v, huM, hvM]
      with x e1 e2 e3 e4 e5 e6 hx hy
    have hsum : |u x + v x| ≤ (K : ℝ) :=
      (abs_add_le _ _).trans (by change |u x| + |v x| ≤ 2 * |M|; linarith [le_abs_self M])
    have hdiff : |u x - v x| ≤ (K : ℝ) :=
      (abs_sub _ _).trans (by change |u x| + |v x| ≤ 2 * |M|; linarith [le_abs_self M])
    change ((1 / 4 : ℝ) • (A - B) : Lp ℝ 2 m) x = _
    rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, e4, e5, e6, Pi.add_apply,
      Pi.sub_apply, sqClamp_of_abs_le hsum, sqClamp_of_abs_le hdiff, smul_eq_mul]
    ring
  · change F.form ((1 / 4 : ℝ) • (A - B)) ((1 / 4 : ℝ) • (A - B)) ≤ _
    rw [F.toClosedForm.form_smul_self _ (F.domain.sub_mem hA.1 hB.1)]
    have h1 := F.toClosedForm.form_sub_self_le hA.1 hB.1
    have h2 := F.toClosedForm.form_add_self_le hu hv
    have h3 := F.toClosedForm.form_sub_self_le hu hv
    have h4 : F.form A A ≤ 16 * M ^ 2 * F.form (u + v) (u + v) := by
      convert hA.2 using 1
      have hKcoe : (K : ℝ) = 2 * |M| := rfl
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hKcoe, mul_pow, sq_abs]
      ring
    have h5 : F.form B B ≤ 16 * M ^ 2 * F.form (u - v) (u - v) := by
      convert hB.2 using 1
      have hKcoe : (K : ℝ) = 2 * |M| := rfl
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hKcoe, mul_pow, sq_abs]
      ring
    have h6 : F.form A A + F.form B B ≤
        64 * M ^ 2 * (F.form u u + F.form v v) := by
      calc
        _ ≤ 16 * M ^ 2 * (F.form (u + v) (u + v) +
            F.form (u - v) (u - v)) := by linarith
        _ ≤ 16 * M ^ 2 * (4 * (F.form u u + F.form v v)) := by
          gcongr
          linarith
        _ = _ := by ring
    nlinarith

                                             
                                            

                                                                   
                     
                                                                                 

                                                           
                                                               

                                                                  
                                     
                                                

                                                                       
                                                                                

                                                 
                                                          

                                               
                                                     
                                        

                                                                                            
                         
                                                                               
                                                                                     
                      

                                               
                                                    
                                                                               

                                       
                                                             
                                                             
                                     
                             
           
                                                       
                                                                   
                                                                                       
                                   
                                
                                      
             
                                               
                                                              
                                                                                  
                                   
                                           

variable [TopologicalSpace X]

                                                                                     
                                                      
                                                                    
                                                      
                                          
                                                                       
                                             
                           
                                                
                                                         

end SubdiffusiveProcess.DirichletForm
