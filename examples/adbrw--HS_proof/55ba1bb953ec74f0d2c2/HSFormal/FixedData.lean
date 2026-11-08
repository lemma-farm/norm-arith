module

public import HSFormal.ChartData

@[expose] public section

/-!
# Section 7: the fixed geometric data from a hypothetical effective action

`HSFormal.FixedData` packages the fixed data of Section 7 of `fullHS_final.md` (L456–539) in the
paper's choice order `(x₀, chart, H) ≺ (ρ₊, ρ, f, Z⁺, T, ρ̃, r, R, t, u) ≺ K_i`:

* the fields are the free choices, with their defining properties;
* `Ω`, `F₀`, `Z⁺`, `f`, `fhat`, `Z₀`, `Z` are derived definitions, given by the paper's formulas;
* the properties (7.1)–(7.9) are theorems below;
* `HSFormal.exists_fixedData`: the data exist for every effective jointly continuous
  `ℤ_[p]`-action on a connected manifold without boundary, given Montgomery's theorem
  `HSFormal.PointwisePeriodicIsPeriodic`.

Degree one (L500) is proved in its homotopy form: the compactified map `fhat` is homotopic rel `∞`
to the identity of `Sⁿ = OnePoint ℝⁿ`, through the homotopy (7.6) and the scaling homotopy of the
pinch. The only further consequence drawn here, `Z⁺ ≠ ∅`, uses the non-contractibility of spheres,
isolated as the explicit hypothesis `HSFormal.SphereSelfMapSurjective`.
-/

noncomputable section

open Set Filter Metric MeasureTheory OnePoint Topology
open scoped unitInterval

namespace HSFormal

/-- The fixed data of Section 7 for an action of `ℤ_[p]` on `M` with charts in `ℝⁿ`. -/
structure FixedData (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type*) [TopologicalSpace M]
    [AddAction ℤ_[p] M] extends ChartData p n M where
  /-- `ρ₊ < 1/4` such that `B̄(0,ρ₊)` misses `Fix(H)` (L483). -/
  ρplus : ℝ
  ρplus_pos : 0 < ρplus
  ρplus_lt : ρplus < 1 / 4
  notMem_fixH : ∀ x ∈ φ.source, ‖φ x‖ ≤ ρplus → x ∉ toChartData.fixH
  /-- The pinch radius `0 < ρ < ρ₊` (L492). -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  ρ_lt : ρ < ρplus
  /-- The equivariant map `ρ̃ : Z⁺ → T = S^{2m-1} ⊆ ℂ^m` of (7.7), continuous with values in `T`
  on an open neighbourhood of `Z⁺`. -/
  m : ℕ
  ρtilde : M → EuclideanSpace ℂ (Fin m)
  ρtilde_spec : ∃ U, IsOpen U ∧ toChartData.carrier ρplus ⊆ U ∧ ContinuousOn ρtilde U ∧
    ∀ x ∈ U, ‖ρtilde x‖ = 1
  ρtilde_vadd : ∀ h ∈ padicPowerSubgroup p j, ∀ x,
    ρtilde (h +ᵥ x) = (padicChar p j h : ℂ) • ρtilde x
  /-- The radii `0 < r < R < t < u < d(y, ∞)` of (7.8), for the round metric, `y = s_ρ(0)`. -/
  r : ℝ
  R : ℝ
  t : ℝ
  u : ℝ
  r_pos : 0 < r
  r_lt_R : r < R
  R_lt_t : R < t
  t_lt_u : t < u
  u_lt : u < roundDist (pinch ρ (0 : EuclideanSpace ℝ (Fin n))) ∞

namespace FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

                                              
                                         

                                                                            
abbrev T : Set (EuclideanSpace ℂ (Fin d.m)) := sphere 0 1

/-- `y = s_ρ(0)` (L519). -/
abbrev y : OnePoint (EuclideanSpace ℝ (Fin n)) := pinch d.ρ 0

/-- `Z₀ = {z : d(y,z) ≥ R}` (7.8). -/
def Z₀ : Set (OnePoint (EuclideanSpace ℝ (Fin n))) := {z | d.R ≤ roundDist d.y z}

/-- The fixed exterior `Z = T × Z₀` (7.8). -/
def Z : Set (EuclideanSpace ℂ (Fin d.m) × OnePoint (EuclideanSpace ℝ (Fin n))) := d.T ×ˢ d.Z₀

open scoped Classical in
/-- The invariant map `f = s_ρ ∘ F₀` on `Ω`, `f = ∞` elsewhere (7.5). -/
def f (x : M) : OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if x ∈ d.Ω then pinch d.ρ (d.F₀ x) else ∞

                                                    
                                       

                                                                                            
                                                                       
                                       

                                                     
                                                  

                                                                           
                                                            

                            
                                                                              
                       
                                                          
                                                                        
                     

                                                                                         
                                    

                                                                           
                                               

                                                                 
                                               
                      

                                                                        
                                               
                                                     

                                       
                                                                                     
                                                         
                                                                   

                                                 
                                                                                
                                              

                                                                         
def chartHomotopyFun (q : I × EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if ‖q.2‖ < 2 then
    pinch d.ρ ((1 - (q.1 : ℝ)) • d.F₀ (d.φ.symm q.2) + (q.1 : ℝ) • q.2)
  else ∞

section Action

variable [ContinuousVAdd ℤ_[p] M]

                                                                      
                                                    
                                                  
                                          
                                   
                               
                                                                      
                                                      
                                    

theorem norm_F₀_symm_sub_le {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ < 2) :
    ‖d.F₀ (d.φ.symm v) - v‖ ≤ 2 * d.D := by
  have h := d.norm_F₀_sub_le (d.symm_mem_Ω hv)
  rwa [d.φ.right_inv (d.mem_target_of_norm_lt hv.le (by norm_num))] at h

/-- (7.6) is `∞` outside the fixed compact set `B̄(0, ρ + 2D)`, uniformly in `t` (L507). -/
theorem chartHomotopyFun_eq_infty {q : I × EuclideanSpace ℝ (Fin n)}
    (hq : d.ρ + 2 * d.D < ‖q.2‖) : d.chartHomotopyFun q = ∞ := by
  obtain ⟨t, v⟩ := q
  simp only at hq
  unfold chartHomotopyFun
  split_ifs with h2
  · apply pinch_of_le
    set F := d.F₀ (d.φ.symm v)
    have hFv := d.norm_F₀_symm_sub_le h2
    have ht0 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.2 t.2.2
    have hw : v = ((1 - (t : ℝ)) • F + (t : ℝ) • v) - (1 - (t : ℝ)) • (F - v) := by
      simp only [smul_sub, sub_smul, one_smul]
      abel
    have h := norm_sub_le ((1 - (t : ℝ)) • F + (t : ℝ) • v) ((1 - (t : ℝ)) • (F - v))
    rw [← hw, norm_smul, Real.norm_of_nonneg ht0] at h
    nlinarith [mul_nonneg t.2.1 (norm_nonneg (F - v))]
  · rfl

                                                                                                
                                                                 
                                          
                                                                                 

                                                                                               
                                                                                                  
                                                                                   
                  
                                                               
                                                            
                        
                                                                                  
                                                                                        
                      

section Homotopy

                                                                   

                                                           

                                                                         
                                                               
                                                                                        
                                                                                           
                                                                                  
                                                                      
                                 
                                                                 
                                                                   
                                                                                          
                                                                                             
                              
                                                  
                         
                                                        
                                                                                        
                                
                                                 
                                                                          
                                                       
                                                   
                                                                   
                                                            
                                                                                                 
                        
                                                  
                                      

                                                                  
                                                                                                   
         
                                                            
                                                                                    
                                                                                                  
                                                          
                               

                                                                                      
                                                                                         
                                                     

       
                                        

                                                 
                                                                         
                                              

                                                              
                                                                                     
                                     
               
                   
                             
                 
                                                   
                              
                               

                                                                                            
                               
                                                                
                                    
                        
                      
                                       
                  
              
                                                    
                             
                       
            
                                         
                                                                             
                    
                                
            
       

                                                                                  
                                                                              
                                                                                      

                                                                
                                                                                      
                                                                
                                                                          
                        
              
                           
                                                       
                     
                         
                                                                                    
                                                                                 
                                                                 
                                                            
                                         
                                    

                                                                      
                                                                              
                                              
                                            

                                                                   

                    

                                           
                                                            
                              
                                                              
                                                  
                       
                                                              
                                                       
                  
                                                       
                                                                          
                                                               
                                                                 
                                             
                                                                      
                   
                                                          
                                                    
                                      

                                                                             

                                                                                       
                                                                                      
                                      
                                                              
                                                     
                                                                  
                                                                
                                                                                           
                                                            
                                                                
                                                         
                                                                          
                                       

                                                                       
                        
                                                     
                                                                  
                                                                                        
                               
                                                          
                                                                                       
                                      
                                
                                             

end Homotopy

end Action

end FixedData

                    

section Existence

                                                                                       
                                                              
                                                                
                                                                     
            

                                                                                  
                                                           
                                                                              
                                                                
                                                                                   
                                                                                       
                                                             
                                                     
                                                                                          
                                                                                       
                                     
                                                                
          
            
                        
          
                         
                
                               
          
                
                           
                       
                                           
                                                             
                                           
                                                                   

                                                                                                 
                                                                                
                                                           
                                                                                                
                                                                
                                                  
                                                                                          
                                                    
                                                                                    
                                                         
                 
                  
                    
                   
                       
                  
                          
                            
          
                
                     
                        
              
          
              
              
                        
                         
                         
                         
                                   

end Existence

end HSFormal
