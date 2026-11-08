module

public import Mathlib

/-!
# Global flows of bounded, Lipschitz, time-dependent vector fields

For a time-dependent vector field `V : ℝ → E → E` which is continuous in time, uniformly bounded
and uniformly Lipschitz in space, we construct the global flow `gflow V t₀ t x` (the value at time
`t` of the solution starting from `x` at time `t₀`) and prove its basic properties: the flow
equation, uniqueness, the cocycle law, Lipschitz bounds and closeness to the identity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal

noncomputable section

namespace AnomDiss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Standing assumptions on a time-dependent vector field: continuity in time, a uniform bound
`M` and a uniform spatial Lipschitz constant `K`. -/
structure GoodField (V : ℝ → E → E) (M K : ℝ≥0) : Prop where
  cont : ∀ x, Continuous fun t => V t x
  bound : ∀ t x, ‖V t x‖ ≤ M
  lip : ∀ t, LipschitzWith K (V t)

namespace GoodField

variable {V : ℝ → E → E} {M K : ℝ≥0}

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma picard (hV : GoodField V M K) (t₀ : ℝ) (x : E) (T : ℝ≥0) :
    IsPicardLindelof V (tmin := t₀ - T) (tmax := t₀ + T)
      ⟨t₀, by constructor <;> simp⟩ x (M * T) 0 M K where
  lipschitzOnWith t _ := (hV.lip t).lipschitzOnWith
  continuousOn x _ := (hV.cont x).continuousOn
  norm_le t _ y _ := hV.bound t y
  mul_max_le := by
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_zero, sub_zero,
      NNReal.coe_mul, le_refl]

                         
                                      
                                                          
                                                                                 
                                
                                                                                     
                                                           

omit [CompleteSpace E] in
/-- Two solutions on a closed interval around `t₀` which agree at `t₀` agree on the interval. -/
lemma eqOn_Icc (hV : GoodField V M K) {α β : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (V t (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (V t (β t)) (Icc a b) t)
    (h : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  have hαc : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousWithinAt
  have hβc : ContinuousOn β (Icc a b) := fun t ht => (hβ t ht).continuousWithinAt
  intro t ht
  rcases le_total t₀ t with h1 | h1
  · have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    have key := ODE_solution_unique (v := V) (K := K) (fun s => hV.lip s)
      (hαc.mono hsub) (fun s hs => ?_) (hβc.mono hsub) (fun s hs => ?_) h
    · exact key ⟨h1, ht.2⟩
    · refine (hα s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hs.1, hs.2⟩
    · refine (hβ s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hs.1, hs.2⟩
  · have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    have key := ODE_solution_unique_of_mem_Icc_left (v := V) (K := K) (s := fun _ => univ)
      (fun s _ => (hV.lip s).lipschitzOnWith)
      (hαc.mono hsub) (fun s hs => ?_) (fun _ _ => trivial) (hβc.mono hsub) (fun s hs => ?_)
      (fun _ _ => trivial) h
    · exact key ⟨ht.1, h1⟩
    · refine (hα s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans ht₀.2⟩
    · refine (hβ s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin ?_
      exact Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans ht₀.2⟩

/-- Global existence of solutions. -/
lemma exists_global (hV : GoodField V M K) (t₀ : ℝ) (x : E) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t, HasDerivAt α (V t (α t)) t := by
  have hloc : ∀ T : ℝ≥0, ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt α (V t (α t)) (Icc (t₀ - T) (t₀ + T)) t := fun T =>
    (hV.picard t₀ x T).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hα using hloc
  have hmem : ∀ T : ℝ≥0, t₀ ∈ Icc (t₀ - T) (t₀ + T) := fun T => by constructor <;> simp
  -- agreement of the local solutions
  have hagree : ∀ T T' : ℝ≥0, T ≤ T' → EqOn (α T) (α T') (Icc (t₀ - T) (t₀ + T)) := by
    intro T T' hTT'
    have hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc (t₀ - T') (t₀ + T') :=
      Icc_subset_Icc (by linarith [NNReal.coe_le_coe.2 hTT']) (by linarith [NNReal.coe_le_coe.2 hTT'])
    refine hV.eqOn_Icc (hmem T) (hα T) (fun t ht => ?_) ((hα0 T).trans (hα0 T').symm)
    exact (hα T' t (hsub ht)).mono hsub
  set τ : ℝ → ℝ≥0 := fun t => ⟨|t - t₀| + 1, by positivity⟩ with hτ
  refine ⟨fun t => α (τ t) t, ?_, fun t => ?_⟩
  · simpa using hα0 (τ t₀)
  · set T : ℝ≥0 := ⟨|t - t₀| + 2, by positivity⟩
    have hT : t ∈ Ioo (t₀ - T) (t₀ + T) := by
      change t₀ - (|t - t₀| + 2) < t ∧ t < t₀ + (|t - t₀| + 2)
      constructor <;> linarith [le_abs_self (t - t₀), neg_le_abs (t - t₀)]
    have hev : (fun s => α (τ s) s) =ᶠ[𝓝 t] α T := by
      have hU : ∀ᶠ s in 𝓝 t, |s - t₀| < |t - t₀| + 1 := by
        have hc : Continuous fun s => |s - t₀| := by fun_prop
        exact hc.continuousAt.eventually_lt continuousAt_const (by linarith)
      filter_upwards [hU] with s hs
      refine hagree (τ s) T ?_ ?_
      · show |s - t₀| + 1 ≤ |t - t₀| + 2; linarith
      · change t₀ - (|s - t₀| + 1) ≤ s ∧ s ≤ t₀ + (|s - t₀| + 1)
        constructor <;> linarith [le_abs_self (s - t₀), neg_le_abs (s - t₀)]
    have hd := (hα T t (Ioo_subset_Icc_self hT)).hasDerivAt (Icc_mem_nhds hT.1 hT.2)
    have heq : α (τ t) t = α T t := hev.eq_of_nhds
    show HasDerivAt (fun s => α (τ s) s) (V t (α (τ t) t)) t
    rw [heq]
    exact hd.congr_of_eventuallyEq hev

end GoodField

open Classical in
/-- The global flow: `gflow V t₀ t x` is the value at time `t` of the solution of `ẏ = V(t, y)`
with `y(t₀) = x` (and `x` itself if no global solution exists). -/
def gflow (V : ℝ → E → E) (t₀ t : ℝ) (x : E) : E :=
  if h : ∃ α : ℝ → E, α t₀ = x ∧ ∀ s, HasDerivAt α (V s (α s)) s then h.choose t else x

namespace GoodField

variable {V : ℝ → E → E} {M K : ℝ≥0}

lemma gflow_spec (hV : GoodField V M K) (t₀ : ℝ) (x : E) :
    gflow V t₀ t₀ x = x ∧ ∀ t, HasDerivAt (fun s => gflow V t₀ s x) (V t (gflow V t₀ t x)) t := by
  have h := hV.exists_global t₀ x
  simp only [gflow, dif_pos h]
  exact h.choose_spec

lemma gflow_self (hV : GoodField V M K) (t₀ : ℝ) (x : E) : gflow V t₀ t₀ x = x :=
  (hV.gflow_spec t₀ x).1

lemma hasDerivAt_gflow (hV : GoodField V M K) (t₀ t : ℝ) (x : E) :
    HasDerivAt (fun s => gflow V t₀ s x) (V t (gflow V t₀ t x)) t :=
  (hV.gflow_spec t₀ x).2 t

lemma continuous_gflow_time (hV : GoodField V M K) (t₀ : ℝ) (x : E) :
    Continuous fun s => gflow V t₀ s x :=
  continuous_iff_continuousAt.2 fun t => (hV.hasDerivAt_gflow t₀ t x).continuousAt

                                                
                                                          
                                                                                
                                                                              

                                                                 
                                                                 
                                                           
                                                                        
                            

                                                            
                                             
                                    

                                                     
                                                                   
                                             
                                                                                 
                                       
                                 
                                                           
                                                                                   
                                                                                  
                      
                             
                                        
                                                           
                                                                                   
                                                                                   
                      
                                           
                                                 

                                            
lemma dist_gflow_le_of_le (hV : GoodField V M K) {t₀ t : ℝ} (h : t₀ ≤ t) (x y : E) :
    dist (gflow V t₀ t x) (gflow V t₀ t y) ≤ dist x y * Real.exp (K * (t - t₀)) := by
  have hd : ∀ z s, HasDerivAt (fun s => gflow V t₀ s z) (V s (gflow V t₀ s z)) s :=
    fun z s => hV.hasDerivAt_gflow t₀ s z
  have := dist_le_of_trajectories_ODE (v := V) (K := K) (a := t₀) (b := t)
    (f := fun s => gflow V t₀ s x) (g := fun s => gflow V t₀ s y) (δ := dist x y)
    (fun s => hV.lip s) (hV.continuous_gflow_time t₀ x).continuousOn
    (fun s _ => (hd x s).hasDerivWithinAt) (hV.continuous_gflow_time t₀ y).continuousOn
    (fun s _ => (hd y s).hasDerivWithinAt) (by simp [hV.gflow_self]) t ⟨h, le_rfl⟩
  exact this

                               
                                                                           

                                           
                                                                                       
                                                                       
                                                           
             
                                                
                              

                                                           
                                                                        
                                      
                                                                
                                                                 
           
                                                               
                                                      
                                                                 
                                                
                                   
                                       
                                                                                
          

                                              
                                                                 
                                                                                     
                                 
                                                                           
                                                                                 
                                                                                        
                       
                              

                                                         
                                                                                          
                                            
                                                  

                                                                                       
                                      

                                                                    
                                                                         
                                                   
                                                            
                                                                               
                                                                                   
           
                                                          
                                                
              
                                                                             
                                                 
              
                                                                       
                                        
                                                                     
                                         
            
                       
                                                           
                                                          
                                                        
                                            
                                                                             
                                                                            
                                                                         
                                                    
                                             
                                                                      
                    

                                                                                          
                                                                      
                                                      
                                                                                          
                                                                  
                                        
                                  
                                                                             
                                                                      
                                                                     
           
                                                                   
                                                   
                                      
                                                                                              
              
                                        
                                                         
                                          
                                         
                                       
                                                              
                            
                               
                                                                        
                    
                                        
                                                                                                   
                       
                                                  
                                                                      
                
                                                           
                                             
                                                                            
                                                                    
                                                           
                                                                           
                                                              
                                                      
                    

                                                                   
                                                          
                                     
                                    
                                      
                                  
                                                                   
                                            
                                                                
                                 
                                      
                                                                                         
                                                   

                                                           
                                                                                    
                                                                          
                                                             
                                                                                         
                                                                                     
                                                                          
                                                             
                                         
                                                                    
                                                                                   
                                                
                                                              
                   
                                                                             
                                                          
                      
                                                 

                                                                  
                                                                              
                                                             
                                                              
                                                                                         
                                 
                                       
                                               
                                                   
                                                                                 
                                                                                             
                                                                         
                                   
                                                                  
                                                                                 
                      
                      
                       
                                           

end GoodField

end AnomDiss
