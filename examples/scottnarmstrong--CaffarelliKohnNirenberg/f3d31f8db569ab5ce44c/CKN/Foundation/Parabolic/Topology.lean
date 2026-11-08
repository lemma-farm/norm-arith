-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Foundation.Parabolic.Basic
import CKN.Statements.SpaceTimeSet
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Topology of parabolic space-time

The parabolic metric of `CKN.Foundation.Parabolic.Basic` is obtained by pulling back the
product metric of `L²(ℝ³) × ℝ` (the time factor being snowflaked) along `parabolicMap`.
This file identifies the resulting topology with the product topology of the spatial
variable and time.  It is the bridge that lets openness and closure of the paper's
space-time carriers be read off from the corresponding statements on `Vec3 × ℝ`: in
particular the space-time set `def:sws`, whose carrier is `Ω × I`, is open for open `Ω`
and `I`, and the interior and closure of a parabolic cylinder are computed from the
Euclidean ball and the intervals `Ioo` and `Icc`.
-/

open scoped Topology
open Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The topology on `ParabolicPoint` is the one induced by `parabolicMap`, i.e. the
pullback of the product topology on `L²(ℝ³) × ℝ`. -/
theorem isInducing_parabolicMap : Topology.IsInducing parabolicMap :=
  Topology.IsInducing.induced parabolicMap

/-- The spatial coordinate is continuous for the parabolic topology: the first factor of
`parabolicMap` is `WithLp.toLp 2`, which is continuous for the `L²` product topology. -/
theorem continuous_fst_parabolicPoint : Continuous (fun p : ParabolicPoint => p.1) := by
  have h : Continuous (fun p : ParabolicPoint => (parabolicMap p).1.ofLp) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
      (continuous_fst.comp isInducing_parabolicMap.continuous)
  have hfun : (fun p : ParabolicPoint => (parabolicMap p).1.ofLp) = (fun p => p.1) := by
    funext p
    exact WithLp.ofLp_toLp 2 p.1
  rwa [hfun] at h

/-- The time coordinate is continuous for the parabolic topology: the second factor of
`parabolicMap` is the snowflaking equivalence, which carries the same topology as `ℝ`. -/
theorem continuous_snd_parabolicPoint : Continuous (fun p : ParabolicPoint => p.2) := by
  have h : Continuous (fun p : ParabolicPoint =>
      Metric.Snowflaking.ofSnowflaking (parabolicMap p).2) :=
    Metric.Snowflaking.continuous_ofSnowflaking.comp
      (continuous_snd.comp isInducing_parabolicMap.continuous)
  have hfun : (fun p : ParabolicPoint =>
      Metric.Snowflaking.ofSnowflaking (parabolicMap p).2) = (fun p => p.2) := by
    funext p
    exact Metric.Snowflaking.ofSnowflaking_toSnowflaking p.2
  rwa [hfun] at h

/-- `parabolicMap`, read on the product `Vec3 × ℝ` with its product topology, is
continuous: both `WithLp.toLp 2` and the snowflaking equivalence are. -/
theorem continuous_parabolicMap_prod :
    Continuous (fun q : Vec3 × ℝ => parabolicMap q) := by
  have h1 : Continuous (fun q : Vec3 × ℝ => WithLp.toLp 2 q.1) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp continuous_fst
  have h2 : Continuous (fun q : Vec3 × ℝ =>
      (Metric.Snowflaking.toSnowflaking q.2 : SnowTime)) :=
    Metric.Snowflaking.continuous_toSnowflaking.comp continuous_snd
  exact h1.prodMk h2

/-- The identity map from the parabolic space-time to `Vec3 × ℝ` with the product
topology is continuous. -/
theorem continuous_parabolicPoint_to_prod :
    Continuous (fun p : ParabolicPoint => (p.1, p.2)) :=
  continuous_fst_parabolicPoint.prodMk continuous_snd_parabolicPoint

/-- The identity map from `Vec3 × ℝ` with the product topology to the parabolic
space-time is continuous; equivalently, the product topology is finer than the parabolic
topology. -/
theorem continuous_prod_to_parabolicPoint :
    Continuous (show Vec3 × ℝ → ParabolicPoint from fun q => (q.1, q.2)) := by
  rw [isInducing_parabolicMap.continuous_iff]
  change Continuous (fun q : Vec3 × ℝ => parabolicMap q)
  exact continuous_parabolicMap_prod

/-- The identity, viewed as a homeomorphism from the parabolic space-time to `Vec3 × ℝ`
with the product topology.  This is the topology bridge: set-theoretic operations on
space-time sets may be performed on the product instead. -/
def parabolicHomeomorph : ParabolicPoint ≃ₜ Vec3 × ℝ where
  toFun := fun p => (p.1, p.2)
  invFun := fun q => ((q.1, q.2) : ParabolicPoint)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_parabolicPoint_to_prod
  continuous_invFun := continuous_prod_to_parabolicPoint

                                                                
                                             

                                                               
                                                                     

                                                                                 
                                                                            
                                                                   
                                       
       
     

                                                                            
                                             
                                          
                                                       
                                                                     
                                      
                                                            
                                                                            
                                                 

                                                                                
                                                              
                                      
                                               

                                                 
                                             

                                                                                        
                           
                                                                        
                                                                                   
         
                                                                                        
                                                             
        
                                                             

                                                                                  
                                                    
                                                          
                                                                             
                                                                                   
         
                                                                                        
                                                             
                                                                  
       
                                                                              
                                                           
     

                                                                               
                                                                                        
                                       
                                                                     
                                                        
                                                              

                                                                                      
                                                                       
                                                         
                                                                                
                                    
                                                                    
                                                         
                                            
                                                                        
                                 

                                                                                
                                                      
                                                                     
                                       
                                                                           
                                      
                                                    
                                    
                                                                    
                                                         
                                           
                                                               
                                 

                                                            
                                                               
                                                                  
                

                                                                  
                                                                              
                    
                                                                              
                                              

end CKN.Foundation.Parabolic
