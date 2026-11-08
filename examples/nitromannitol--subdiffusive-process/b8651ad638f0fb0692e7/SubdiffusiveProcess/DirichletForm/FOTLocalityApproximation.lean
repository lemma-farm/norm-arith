module

public import SubdiffusiveProcess.DirichletForm.FOTLocalityCore

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- Continuous core approximations with a uniform energy bound. -/
structure CoreApproximation (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) (u : Lp ℝ 2 m) where
  seq : ℕ → Lp ℝ 2 m
  rep : ℕ → X → ℝ
  mem_domain : ∀ n, seq n ∈ F.domain
  continuous : ∀ n, Continuous (rep n)
  compact : ∀ n, HasCompactSupport (rep n)
  support : ∀ n, tsupport (rep n) ⊆ U
  ae_rep : ∀ n, ⇑(seq n) =ᵐ[m] rep n
  tendsto : Tendsto seq atTop (𝓝 u)
  bound : ℝ
  energy_le : ∀ n, F.form (seq n) (seq n) ≤ bound

                                                                                                
                                                          
                                           
                                                                                 

                                                                                                  
                                                                          
                                                
                                
                                                               
                                                         
                                        
                                                            
                                 

                                                                                      
                                                      
                                                                               
                                                                          
                                                  
                                                                          
                                                   
                                      
                                                                             
                                                          
           
                                         
           
                      
                                               
                                   
                                     
                                       
                                      
                                                            
                                                                 
           
                                                             
                   
                                                   
           
                                  
                                                                                      
                             
                                                                                        
        
                                                               
               
                         
                                                  
                                 
                                                   
                                     
                        
           
            
                                     
                     
                                                  
                                    
                                                           
                   
                                                    
                                                  
                                                         
                                                           
                                                                        
                                        

                                                                               
theorem CoreApproximation.exists_plateau [T2Space X]
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {u : Lp ℝ 2 m}
    (a : CoreApproximation F U u) {R : ℝ≥0} (haR : ∀ n x, |a.rep n x| ≤ R)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) {f : X → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hwae : ⇑w =ᵐ[m] f) (hf01 : ∀ x, f x ∈ Icc 0 1)
    {c : ℝ} (hfu : ∀ᵐ x ∂m, (c - u x) * f x = 0) :
    ∃ b : CoreApproximation F U u,
      ∀ n x, f x = 1 → b.rep n x = c := by
  have haM : ∀ n, ∀ᵐ x ∂m, |a.seq n x| ≤ (R : ℝ) + 1 := by
    intro n
    filter_upwards [a.ae_rep n] with x hx
    rw [hx]
    linarith [haR n x]
  have hwM : ∀ᵐ x ∂m, |w x| ≤ (R : ℝ) + 1 := by
    filter_upwards [hwae] with x hx
    rw [hx, abs_of_nonneg (hf01 x).1]
    linarith [(hf01 x).2, R.coe_nonneg]
  choose p hpD hpae hpE using fun n =>
    exists_mul_mem_form_le F (a.mem_domain n) hw (haM n) hwM
  let v : ℕ → Lp ℝ 2 m := fun n => a.seq n - p n + c • w
  let g : ℕ → X → ℝ := fun n x => a.rep n x - a.rep n x * f x + c * f x
  have hvD : ∀ n, v n ∈ F.domain := fun n =>
    F.domain.add_mem (F.domain.sub_mem (a.mem_domain n) (hpD n)) (F.domain.smul_mem c hw)
  have hgae : ∀ n, ⇑(v n) =ᵐ[m] g n := by
    intro n
    filter_upwards [Lp.coeFn_add (a.seq n - p n) (c • w),
      Lp.coeFn_sub (a.seq n) (p n), Lp.coeFn_smul c w, hpae n, a.ae_rep n, hwae]
      with x h1 h2 h3 h4 h5 h6
    change (a.seq n - p n + c • w : Lp ℝ 2 m) x = _
    rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul, h4, h5, h6]
  have hnorm : ∀ n, ‖v n - u‖ ≤ ‖a.seq n - u‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (v n) u, Lp.coeFn_sub (a.seq n) u,
      hgae n, a.ae_rep n, hfu] with x h1 h2 h3 h4 heq
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, Real.norm_eq_abs, Real.norm_eq_abs]
    change |a.rep n x - a.rep n x * f x + c * f x - u x| ≤ |a.rep n x - u x|
    calc
      _ = |(a.rep n x - u x) * (1 - f x)| := by
        congr 1
        nlinarith [heq]
      _ = |a.rep n x - u x| * |1 - f x| := abs_mul _ _
      _ ≤ |a.rep n x - u x| := by
        apply mul_le_of_le_one_right (abs_nonneg _)
        exact abs_le.mpr ⟨by linarith [(hf01 x).2], by linarith [(hf01 x).1]⟩
  have hvE : ∀ n, F.form (v n) (v n) ≤
      4 * a.bound + 32 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w) +
        2 * c ^ 2 * F.form w w := by
    intro n
    have hp := (hpE n).trans (show _ ≤
        8 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w) by
      gcongr
      exact a.energy_le n)
    have h1 := F.toClosedForm.form_sub_self_le (a.mem_domain n) (hpD n)
    have h2 := F.toClosedForm.form_add_self_le
      (F.domain.sub_mem (a.mem_domain n) (hpD n)) (F.domain.smul_mem c hw)
    rw [F.toClosedForm.form_smul_self c hw] at h2
    change F.form (a.seq n - p n + c • w) (a.seq n - p n + c • w) ≤ _
    linarith [a.energy_le n]
  refine ⟨{
    seq := v
    rep := g
    mem_domain := hvD
    continuous := fun n => ((a.continuous n).sub ((a.continuous n).mul hf)).add
      (continuous_const.mul hf)
    compact := fun n => ((a.compact n).sub hfc.mul_left).add hfc.mul_left
    support := ?_
    ae_rep := hgae
    tendsto := tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) hnorm
        (tendsto_iff_norm_sub_tendsto_zero.mp a.tendsto))
    bound := 4 * a.bound + 32 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w) +
      2 * c ^ 2 * F.form w w
    energy_le := hvE
  }, ?_⟩
  · intro n
    have hs : Function.support (g n) ⊆ tsupport (a.rep n) ∪ tsupport f := by
      intro x hx
      by_contra h
      have h1 : x ∉ tsupport (a.rep n) := fun hx => h (Or.inl hx)
      have h2 : x ∉ tsupport f := fun hx => h (Or.inr hx)
      have ha0 := image_eq_zero_of_notMem_tsupport h1
      have hf0 := image_eq_zero_of_notMem_tsupport h2
      exact hx (by simp [g, ha0, hf0])
    exact (closure_minimal hs (isClosed_closure.union isClosed_closure)).trans
      (union_subset (a.support n) hfU)
  · intro n x hx
    change a.rep n x - a.rep n x * f x + c * f x = c
    rw [hx]
    ring

end SubdiffusiveProcess.DirichletForm
