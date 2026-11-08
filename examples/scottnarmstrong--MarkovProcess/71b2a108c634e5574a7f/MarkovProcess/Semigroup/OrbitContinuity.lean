/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Semigroup.Basic
import MarkovProcess.Semigroup.StrongOperatorLimit

/-!
# Continuity of semigroup orbits from continuity at zero

For a contractive semigroup, strong convergence to the identity at time zero
propagates to continuity of every orbit at every nonnegative time.  Contractivity also upgrades
strong continuity to joint continuity in the time and the vector, in the form
`continuous_operator_apply`.
-/

open Filter Topology

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A contractive semigroup whose orbits converge strongly to the identity at
zero has continuous orbits on all of `NNReal`. -/
theorem continuous_orbit_of_tendsto_zero
    (T : NNReal → E →L[ℝ] E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hcontract : ∀ t, ‖T t‖ ≤ 1)
    (htend : ∀ x, Tendsto (fun t ↦ T t x) (nhds 0) (nhds x))
    (x : E) :
    Continuous (fun t ↦ T t x) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  obtain ⟨δ, hδ, hnear⟩ := (Metric.tendsto_nhds_nhds.mp (htend x)) ε hε
  refine ⟨δ, hδ, fun s hst ↦ ?_⟩
  rcases le_total t s with hts | hst'
  · have hgap : dist (s - t) 0 < δ := by
      simpa only [NNReal.dist_eq, NNReal.coe_sub hts, NNReal.coe_zero, sub_zero,
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hts))] using hst
    have hsmall := hnear hgap
    have hs : T s x = T t (T (s - t) x) := by
      rw [← ContinuousLinearMap.comp_apply, ← hadd, add_comm, tsub_add_cancel_of_le hts]
    rw [hs]
    calc
      dist (T t (T (s - t) x)) (T t x) ≤ dist (T (s - t) x) x := by
        calc
          _ ≤ ‖T t‖ * dist (T (s - t) x) x := (T t).dist_le_opNorm _ _
          _ ≤ 1 * dist (T (s - t) x) x :=
            mul_le_mul_of_nonneg_right (hcontract t) dist_nonneg
          _ = _ := one_mul _
      _ < ε := hsmall
  · have hgap : dist (t - s) 0 < δ := by
      rw [dist_comm] at hst
      simpa only [NNReal.dist_eq, NNReal.coe_sub hst', NNReal.coe_zero, sub_zero,
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst'))] using hst
    have hsmall := hnear hgap
    have ht : T t x = T s (T (t - s) x) := by
      rw [← ContinuousLinearMap.comp_apply, ← hadd, add_comm, tsub_add_cancel_of_le hst']
    rw [ht, dist_comm]
    calc
      dist (T s (T (t - s) x)) (T s x) ≤ dist (T (t - s) x) x := by
        calc
          _ ≤ ‖T s‖ * dist (T (t - s) x) x := (T s).dist_le_opNorm _ _
          _ ≤ 1 * dist (T (t - s) x) x :=
            mul_le_mul_of_nonneg_right (hcontract s) dist_nonneg
          _ = _ := one_mul _
      _ < ε := hsmall

namespace StronglyContinuousContractionSemigroup

                                                                                               
                                                                                                
                                         
                                                                                
                                                                 
                                             
                                          
                                  
         
                                                                          
                                                                                      
                   

                                                                            
                                                 
def ofTendstoZero
    (T : NNReal → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s + t) = (T s).comp (T t))
    (hcontract : ∀ t, ‖T t‖ ≤ 1)
    (htend : ∀ x, Tendsto (fun t ↦ T t x) (nhds 0) (nhds x)) :
    StronglyContinuousContractionSemigroup E where
  operator := T
  operator_zero := hzero
  operator_add := hadd
  opNorm_le_one := hcontract
  continuous_orbit := continuous_orbit_of_tendsto_zero T hadd hcontract htend

end StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup
