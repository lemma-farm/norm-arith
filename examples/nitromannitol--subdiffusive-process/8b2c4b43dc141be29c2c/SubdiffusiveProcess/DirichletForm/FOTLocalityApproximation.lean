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

                                                                                                
                                                          
                                           
                                                                                 

                                                                                                  
                                                                          
                                                
                                
                                                               
                                                         
                                        
                                                            
                                 

                                                                                      
theorem CoreApproximation.exists_supported [T2Space X]
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {u : Lp ℝ 2 m}
    (a : CoreApproximation F U u) {R : ℝ≥0} (haR : ∀ n x, |a.rep n x| ≤ R)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) {f : X → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hwae : ⇑w =ᵐ[m] f) (hf01 : ∀ x, f x ∈ Icc 0 1)
    (hfu : ∀ᵐ x ∂m, u x * f x = u x) :
    ∃ b : CoreApproximation F U u, ∀ n, tsupport (b.rep n) ⊆ tsupport f := by
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
  have hprep : ∀ n, ⇑(p n) =ᵐ[m] (fun x => a.rep n x * f x) := by
    intro n
    filter_upwards [hpae n, a.ae_rep n, hwae] with x hx hy hz
    rw [hx, hy, hz]
  have hnorm : ∀ n, ‖p n - u‖ ≤ ‖a.seq n - u‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (p n) u, Lp.coeFn_sub (a.seq n) u, hpae n, hwae, hfu]
      with x hx hy hz hfξ heq
    rw [hx, hy, Pi.sub_apply, Pi.sub_apply, hz, hfξ, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |a.seq n x * f x - u x| = |(a.seq n x - u x) * f x| := by
        congr 1
        rw [sub_mul, heq]
      _ = |a.seq n x - u x| * |f x| := abs_mul _ _
      _ ≤ |a.seq n x - u x| := by
        apply mul_le_of_le_one_right (abs_nonneg _)
        rw [abs_of_nonneg (hf01 x).1]
        exact (hf01 x).2
  refine ⟨{
    seq := p
    rep := fun n x => a.rep n x * f x
    mem_domain := hpD
    continuous := fun n => (a.continuous n).mul hf
    compact := fun n => hfc.mul_left
    support := fun n => tsupport_mul_subset_right.trans hfU
    ae_rep := hprep
    tendsto := tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) hnorm
        (tendsto_iff_norm_sub_tendsto_zero.mp a.tendsto))
    bound := 8 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w)
    energy_le := fun n => (hpE n).trans (by gcongr; exact a.energy_le n)
  }, fun n => tsupport_mul_subset_right⟩

                                                                               
                                                    
                                                                               
                                                                          
                                                  
                                                                          
                                                   
                                                  
                                  
                                          
                                                          
           
                                         
           
                      
                                               
                                   
                                     
                                       
                                      
                                                            
                                                        
                                                                       
                                            
                                                                                         
                                         
           
                                                         
                                                                                
                              
                                                   
                                                                                       
                                                   
           
                                  
                                                                   
                                                     
                                                                                       
                                                                            
        
                                               
               
                       
                                                      
                                 
                                                   
                                                                             
                                      
                                                                     
                                    
           
                                      
                                                         
            
                          
                                                                       
                                              
                                                                          
                                                 
                                                                     
                            
           
            
            
                     
                                                                               
                               
                                                                         
                 
                  
                                                    
                                                  
                                                         
                                                                            
                            
                    
        
           
                                                                            
                
                 
                                                                 
                                                         
                                                     
                                                     
                                      
                                                                              
                                      
                
                                                    
           
        

end SubdiffusiveProcess.DirichletForm
