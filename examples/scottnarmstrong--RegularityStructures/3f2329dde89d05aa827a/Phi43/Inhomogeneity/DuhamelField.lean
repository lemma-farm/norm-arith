/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.MildSmooth
public import RegularityStructures.PDE.MildTime
public import RegularityStructures.PDE.SpatialDeriv
public import RegularityStructures.Abstract.Datum.Deriv

/-!
# The Duhamel field of a smooth periodic forcing

For a smooth spatially periodic `g : ℝ × ℝ³ → ℝ` (`PerSmooth g`), the Duhamel field
`duhamelField hg (t, y) = ∫₀ᵗ P_{t-r} g(r, ·) dr (y)` for `t > 0` (and `0` for `t ≤ 0`) is the mild
solution of `∂_t u = Δu + g`, `u(0) = 0` (`isMildSolution_duhamelPath`).  By the mild-solution
theory of `PDE/` it is smooth on `{t > 0}` (`smoothPos_duhamelField`).

This is the function `θ_s(t) = ∫_s^t P_{t-r} ζ(r) dr` of the restart datum of the `Φ⁴₃` fixed point
(with the time `t - s` as the first coordinate).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE

/-- A smooth function on `ℝ × ℝ³`, periodic in the space variables (the lift of a smooth function
on `ℝ × T³`). -/
structure PerSmooth (g : ParabolicSpace → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  periodic : ∀ (z : ParabolicSpace) (c : Fin 3 → ℝ), torusProj c = 0 → g (z.1, z.2 + c) = g z

variable {g : ParabolicSpace → ℝ}

/-- The forcing `G(t, x, v) = g(t, x)` as a continuous function on `ℝ × T³ × ℝ`. -/
def forcing (hg : PerSmooth g) : C(ℝ × Torus3 × ℝ, ℝ) :=
  descend3 (fun p : ℝ × (Fin 3 → ℝ) × ℝ => g (p.1, p.2.1))
    (hg.smooth.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
    (fun s a b v hab => by
      have hc : torusProj (b - a) = 0 := (torusProj_eq_iff_sub b a).1 hab.symm
      have := hg.periodic (s, a) (b - a) hc
      simpa using this.symm)

/-- The path `s ↦ g(s, ·) ∈ C(T³)`. -/
def forcePath (hg : PerSmooth g) (s : ℝ) : C(Torus3, ℝ) :=
  nemytskii (forcing hg) s 0

/-- The Duhamel field `(t, y) ↦ ∫₀ᵗ P_{t-r} g(r, ·) dr (y)` for `t > 0`, and `0` for `t ≤ 0`. -/
def duhamelField (hg : PerSmooth g) : ParabolicSpace → ℝ :=
  fun z => if 0 < z.1 then duhamel (forcePath hg) z.1 (torusProj z.2) else 0

end RegularityStructures.Inhomogeneity

end

public section

open scoped ContDiff

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE Set Filter Topology

variable {g : ParabolicSpace → ℝ}

theorem PerSmooth.eq_of_torusProj_eq (hg : PerSmooth g) (s : ℝ) {a b : Fin 3 → ℝ}
    (hab : torusProj a = torusProj b) : g (s, a) = g (s, b) := by
  have hc : torusProj (b - a) = 0 := (torusProj_eq_iff_sub b a).1 hab.symm
  have := hg.periodic (s, a) (b - a) hc
  simpa using this.symm

                                                                       
                                                   

theorem forcePath_apply (hg : PerSmooth g) (s : ℝ) (y : Fin 3 → ℝ) :
    forcePath hg s (torusProj y) = g (s, y) := by
  change g (s, torusRep (torusProj y)) = g (s, y)
  exact hg.eq_of_torusProj_eq s (torusProj_torusRep _)

theorem continuous_forcePath (hg : PerSmooth g) : Continuous (forcePath hg) :=
  continuous_nemytskii_comp (forcing hg) (u := fun _ => (0 : C(Torus3, ℝ))) continuous_const

                                               
                                                                                 
          
                                                             
                                                      

                                                        
                                                
                         
                                                                             

                                                                                          
                                              

                                                                             
                                                               
                                                                  
           
                                                                                              
            
         
       
                                     

                                                                        
                                                                                          
                                              
                                                               
                                                                                 
                                                                    

theorem duhamelField_of_pos (hg : PerSmooth g) {z : ParabolicSpace} (hz : 0 < z.1) :
    duhamelField hg z = duhamel (forcePath hg) z.1 (torusProj z.2) := by
  simp [duhamelField, hz]

                                                                                       
                               
                                  

                                                                                           
                                                        
                          
                                                                                                  
                                                                       
                                            
                                       

end RegularityStructures.Inhomogeneity

end
