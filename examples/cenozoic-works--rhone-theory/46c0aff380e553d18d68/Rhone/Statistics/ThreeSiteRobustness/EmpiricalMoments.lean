/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib
public import Rhone.Statistics.ThreeTipSites.Channel
public import Rhone.Statistics.Identifiability.FinitePanelConcentration
public import Rhone.Statistics.ThreeSiteRobustness.UniformMargin
/-! # Empirical five-feature score on iid whole linked blocks -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteRobustness
open ThreeSiteSeparator ThreeTipSites                 
open Identifiability.FinitePanelSampling

variable {K N : ℕ}

                                                 
                                                       

theorem empirical_feature_bound (hK : 3 ≤ K) (hN : 0 < N)
    (x : Fin N → Panel K 3) (i : Fin 5) : |sampleMean (panelFeatures i) x| ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sampleMean, abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    ∑ n : Fin N, |panelFeatures i (x n)| ≤ ∑ _n : Fin N, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => panelFeatures_bounded hK i (x n)
    _ = 1 * (N : ℝ) := by simp

                                                                                 
                                               
                                                     
                                     
     

                                                                                               
                                                                           
                                  
                                             

                                                                           
                                                                                
                             
                                                                 

end Rhone.Statistics.ThreeSiteRobustness
