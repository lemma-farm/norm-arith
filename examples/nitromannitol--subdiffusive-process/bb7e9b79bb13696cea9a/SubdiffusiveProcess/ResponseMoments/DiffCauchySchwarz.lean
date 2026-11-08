module

public import SubdiffusiveProcess.ResponseMoments.BilinearCS
public import Mathlib.Tactic

@[expose] public section

/-!
# The relative form of two candidate energies, Lemma `mfd:lem-diff`

`mfd:lem-diff`: with
`m Γ_E ≤ Γ_F ≤ M Γ_E` and `c ∈ [m, M]`, the relative measure
`Γ_D = Γ_F - c Γ_E` satisfies
`|Γ_D(u,v)|(B) ≤ Δ √(Γ_E(u)(B) Γ_E(v)(B))` with `Δ = M - m`.
The proof is matrix Cauchy--Schwarz applied to the two nonnegative
combinations `Δ Γ_E ± Γ_D`, exactly as in paper label `mfd:lem-diff`.
-/

open Real

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- From the squared Cauchy--Schwarz inequality to the absolute value. -/
theorem abs_bilin_le_sqrt {B : V → V → ℝ} (hsymm : ∀ u v, B u v = B v u)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ (c : ℝ) (u v : V), B (c • u) v = c * B u v)
    (hnonneg : ∀ u, 0 ≤ B u u) (u v : V) :
    |B u v| ≤ Real.sqrt (B u u * B v v) := by
  have hsq := bilin_sq_le hsymm hadd hsmul hnonneg u v
  have hy : (0 : ℝ) ≤ B u u * B v v := mul_nonneg (hnonneg u) (hnonneg v)
  refine (Real.le_sqrt (abs_nonneg _) hy).mpr ?_
  rwa [sq_abs]

variable {X : Type*} [MeasurableSpace X]

theorem diff_measure_cauchy_schwarz (E F : LocalEnergy V X) (m M c : ℝ)
    (hmc : m ≤ c) (hcM : c ≤ M)
    (hlower : ∀ (w : V) (s : Set X), MeasurableSet s → m * E.gam w w s ≤ F.gam w w s)
    (hupper : ∀ (w : V) (s : Set X), MeasurableSet s → F.gam w w s ≤ M * E.gam w w s)
    (u v : V) (s : Set X) (hs : MeasurableSet s) :
    |_root_.SubdiffusiveProcess.ResponseMoments.LocalEnergy.diffGam c E F u v s| ≤
      (M - m) * Real.sqrt (E.gam u u s * E.gam v v s) := by
  classical
  set Del : ℝ := M - m with hDel
  set P : V → V → ℝ := fun w w' =>
    Del * E.gam w w' s + (F.gam w w' s - c * E.gam w w' s) with hP
  set N : V → V → ℝ := fun w w' =>
    Del * E.gam w w' s - (F.gam w w' s - c * E.gam w w' s) with hN
  have hEnn : ∀ w : V, 0 ≤ E.gam w w s := fun w => E.gam_nonneg w s
  have hPsymm : ∀ a b, P a b = P b a := by
    intro a b; simp only [hP, E.gam_symm a b s, F.gam_symm a b s]
  have hNsymm : ∀ a b, N a b = N b a := by
    intro a b; simp only [hN, E.gam_symm a b s, F.gam_symm a b s]
  have hPadd : ∀ a b w, P (a + b) w = P a w + P b w := by
    intro a b w; simp only [hP, E.gam_add_left, F.gam_add_left]; ring
  have hNadd : ∀ a b w, N (a + b) w = N a w + N b w := by
    intro a b w; simp only [hN, E.gam_add_left, F.gam_add_left]; ring
  have hPsmul : ∀ (r : ℝ) a b, P (r • a) b = r * P a b := by
    intro r a b; simp only [hP, E.gam_smul_left, F.gam_smul_left]; ring
  have hNsmul : ∀ (r : ℝ) a b, N (r • a) b = r * N a b := by
    intro r a b; simp only [hN, E.gam_smul_left, F.gam_smul_left]; ring
  have hPnn : ∀ w : V, 0 ≤ P w w := by
    intro w
    have h1 := hlower w s hs
    have h2 := hEnn w
    simp only [hP, hDel]
    nlinarith
  have hNnn : ∀ w : V, 0 ≤ N w w := by
    intro w
    have h1 := hupper w s hs
    have h2 := hEnn w
    simp only [hN, hDel]
    nlinarith
  have hPle : ∀ w : V, P w w ≤ 2 * Del * E.gam w w s := by
    intro w
    have h1 := hupper w s hs
    have h2 := hEnn w
    simp only [hP, hDel]
    nlinarith
  have hNle : ∀ w : V, N w w ≤ 2 * Del * E.gam w w s := by
    intro w
    have h1 := hlower w s hs
    have h2 := hEnn w
    simp only [hN, hDel]
    nlinarith
  have hPcs := abs_bilin_le_sqrt hPsymm hPadd hPsmul hPnn u v
  have hNcs := abs_bilin_le_sqrt hNsymm hNadd hNsmul hNnn u v
  have hd : 0 ≤ Del := by simp only [hDel]; linarith
  have hPNu : P u u + N u u = 2 * Del * E.gam u u s := by simp only [hP, hN]; ring
  have hPNv : P v v + N v v = 2 * Del * E.gam v v s := by simp only [hP, hN]; ring
  have hcs2 := sqrt_mul_add_sqrt_mul_le (hPnn u) (hNnn u) (hPnn v) (hNnn v)
  rw [hPNu, hPNv] at hcs2
  have hkey : Real.sqrt ((2 * Del * E.gam u u s) * (2 * Del * E.gam v v s)) =
      2 * Del * Real.sqrt (E.gam u u s * E.gam v v s) := by
    have hrw : (2 * Del * E.gam u u s) * (2 * Del * E.gam v v s) =
        (2 * Del) ^ 2 * (E.gam u u s * E.gam v v s) := by ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hkey] at hcs2
  have hsum : |P u v| + |N u v| ≤
      2 * Del * Real.sqrt (E.gam u u s * E.gam v v s) := by
    linarith [hPcs, hNcs, hcs2]
  have hDeq : _root_.SubdiffusiveProcess.ResponseMoments.LocalEnergy.diffGam c E F u v s = (P u v - N u v) / 2 := by
    simp only [hP, hN, _root_.SubdiffusiveProcess.ResponseMoments.LocalEnergy.diffGam]
    ring
  have habs : |P u v - N u v| ≤ |P u v| + |N u v| := by
    rcases abs_cases (P u v - N u v) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> [skip; skip] <;>
      · rcases abs_cases (P u v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (N u v) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
          rw [h1, h2] <;> linarith
  rw [hDeq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hDel' : Del = M - m := hDel
  nlinarith [habs, hsum, Real.sqrt_nonneg (E.gam u u s * E.gam v v s)]


                                                                             
                                           
                                                                          
                                                         
                                             
                                                            
                                            
                                                        
                                                       
                                                 
                                              
                                                       
                                                                              
                                                
                                                     
                              
                                                                         
                 
                                                 
                                                    
                                                 
                                                                
                                                                       
                                                                           
                                                              
                                                                
                                           
                                                      
             
              
                                                                                      
                  
                       
                           
                                                                                     
                                             
                       
                                              
                   
                         

                                                                                          
                                                                      
                                                                        
                                     
                                        
                                  
                                                             
                                                      
                                                
                                                              
                                                                 
                                         
              
              
                                                       
                                        
                                   
                                                      

end ResponseMoments
end SubdiffusiveProcess
