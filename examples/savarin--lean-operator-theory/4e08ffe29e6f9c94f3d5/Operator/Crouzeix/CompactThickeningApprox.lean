/-
# Compact metric-thickening approximations

The open thickenings in `SmoothApprox.lean` supply the convex domains used by
the analytic argument.  At the same radii, their closed metric thickenings
form a decreasing compact exhaustion and contain the corresponding domain
frontiers.  These are the compact control sets used by the limiting Palencia
assembly.

## Main declarations

* `compactThickeningApprox` -- the closed thickening at radius `1 / (n + 1)`.
* `compactThickeningApprox_infinite` -- every stage over a nonempty set is
  infinite.
* `compactThickeningApprox_spec` -- antitonicity, compactness, nonemptiness,
  and exact intersection of the compact exhaustion.
* `frontier_convexThickeningApprox_subset_compactThickeningApprox` -- the
  open-stage frontier lies in the compact control set at the same radius.
-/
import Operator.Crouzeix.SmoothApprox
import Mathlib
open Metric Set

private theorem smoothApproxRadius_pos_compact (n : ℕ) : 0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity

private theorem smoothApproxRadius_antitone : Antitone smoothApproxRadius := by
  intro m n hmn
  unfold smoothApproxRadius
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hmn 1

/-- The closed metric thickening of `K` at radius `1 / (n + 1)`. -/
noncomputable def compactThickeningApprox (K : Set ℂ) (n : ℕ) : Set ℂ :=
  Metric.cthickening (smoothApproxRadius n) K

                                                                              
                                                                  
                                                            
                                                                           
                             
                                                                          
                                                                      
                                 
                                           
                                                                 
                                                  
                  
                                
                                                 

                                                                        
                                                                           
theorem compactThickeningApprox_spec (K : Set ℂ) (hcompact : IsCompact K)
    (hnonempty : K.Nonempty) :
    Antitone (compactThickeningApprox K) ∧
      (∀ n, IsCompact (compactThickeningApprox K n)) ∧
      (∀ n, (compactThickeningApprox K n).Nonempty) ∧
      (⋂ n, compactThickeningApprox K n) = K := by
  have hanti : Antitone (compactThickeningApprox K) := by
    intro m n hmn
    exact Metric.cthickening_mono (smoothApproxRadius_antitone hmn) K
  have hstageCompact : ∀ n, IsCompact (compactThickeningApprox K n) :=
    fun _ ↦ hcompact.cthickening
  have hstageNonempty : ∀ n, (compactThickeningApprox K n).Nonempty :=
    fun n ↦ hnonempty.mono
      (Metric.self_subset_cthickening (E := K) (δ := smoothApproxRadius n))
  let radii : Set ℝ := Set.range smoothApproxRadius
  have hradii_small : ∀ ε, 0 < ε → (radii ∩ Set.Ioc 0 ε).Nonempty := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨smoothApproxRadius n, ⟨⟨n, rfl⟩, ?_⟩⟩
    exact ⟨smoothApproxRadius_pos_compact n, hn.le⟩
  have hclosure := Metric.closure_eq_iInter_cthickening' K radii hradii_small
  rw [hcompact.isClosed.closure_eq] at hclosure
  refine ⟨hanti, hstageCompact, hstageNonempty, ?_⟩
  calc
    (⋂ n, compactThickeningApprox K n) =
        ⋂ δ ∈ radii, Metric.cthickening δ K := by
      ext x
      simp only [Set.mem_iInter, compactThickeningApprox]
      constructor
      · intro hx δ hδ
        obtain ⟨n, rfl⟩ := hδ
        exact hx n
      · intro hx n
        exact hx (smoothApproxRadius n) ⟨n, rfl⟩
    _ = K := hclosure.symm

                                                                       
                                 
                                                                      
                         
                                                                             
                                     
                                                                           
