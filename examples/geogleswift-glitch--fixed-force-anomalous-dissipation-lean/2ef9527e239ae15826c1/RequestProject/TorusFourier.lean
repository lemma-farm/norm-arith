module

public import RequestProject.Basic

/-!
# Fourier analysis on `𝕋²`

Characters, Fourier coefficients and Parseval's identity on the two-dimensional torus
(Definition 1.1), for continuous periodic functions represented on the unit cell.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix NNReal

noncomputable section

namespace AnomDiss

/-- The character `e_ξ(y) = e^{2πi ξ·y}` (for `ξ ∈ ℝ²`; for `ξ ∈ ℤ²` this is `e_ℓ`). -/
def expChar (ξ : Pt 2) (y : Pt 2) : ℂ := Complex.exp (2 * π * Complex.I * (dot ξ y : ℂ))

                                                                                
                                                                                       

                                                                                            
                
                        
         
                                                                
                 

                                                                                      
                
                        
         
                                                                
                 

                                                                  
                    
          

                                                         
                                       
                                                                    
                          

                                                         
                                                                                 
                                      
         
           
                     
                                           
                     

                                                                                       
                             
                                         
                                                                                                                   
                       
                                             

                                                                                           
                                                        

section TorusParseval

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The projection `ℝ² → 𝕋²`. -/
def torusProj (y : Pt 2) : UnitAddTorus (Fin 2) := fun i => (y i : UnitAddCircle)

lemma measurePreserving_torusProj :
    MeasurePreserving torusProj (volume.restrict (cell 2)) volume := by
  have hcell : cell 2 = Set.univ.pi (fun _ : Fin 2 => Icc (0:ℝ) 1) := by
    rw [cell, ← Set.pi_univ_Icc]; rfl
  have h1 : (volume : Measure (Pt 2)).restrict (cell 2) =
      Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ).restrict (Ioc 0 (0 + 1))) := by
    rw [hcell, volume_pi, Measure.restrict_pi_pi]
    congr 1; funext i
    rw [zero_add]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  rw [h1]
  have hm : MeasurePreserving ((↑) : ℝ → UnitAddCircle) ((volume : Measure ℝ).restrict (Ioc 0 (0 + 1)))
      AddCircle.haarAddCircle := by
    have := UnitAddCircle.measurePreserving_mk 0
    rwa [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] at this
  exact measurePreserving_pi _ (fun _ => AddCircle.haarAddCircle) (fun _ => hm)


/-- Representative in `[0,1)` of a point of the unit circle. -/
noncomputable def circRep (x : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 0 x : ℝ)

lemma measurable_circRep : Measurable circRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

                                                                     
                                                                      
                                                 

lemma circRep_coe (y : ℝ) : ∃ n : ℤ, circRep (y : UnitAddCircle) = y + n := by
  have h : ((circRep (y : UnitAddCircle) : ℝ) : UnitAddCircle) = (y : UnitAddCircle) :=
    (AddCircle.equivIco 1 0).symm_apply_apply _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h)
  refine ⟨-k, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  push_cast; linarith


/-- The function on `𝕋²` induced by a function on `ℝ²` (via representatives in `[0,1)²`). -/
noncomputable def torusLift {α : Type*} (h : Pt 2 → α) (x : UnitAddTorus (Fin 2)) : α :=
  h (fun i => circRep (x i))

lemma torusLift_proj {α : Type*} (h : Pt 2 → α) (hp : IsPeriodic h) (y : Pt 2) :
    torusLift h (torusProj y) = h y := by
  choose n hn using fun i => circRep_coe (y i)
  have : (fun i => circRep (torusProj y i)) = y + intVec n := by
    funext i; simp [torusProj, hn i, intVec]
  rw [torusLift, this, hp]

                                                                                           
                                                                                                  

                                                                                            
                                                                                           
                   
                                                                                           

                                                                                 
                                                                         
                                                   
                                                   
                                                                           

                                                     
                                                                      
                                                         
                               
                                      
         
           
                     
                                           
                     

                                                                          
                                                                              
                                                                    
                                                                                
                                                                                       
                                      
                                                                           
                                                            
                                                               
                                                                                               
                                                                                       
                                                        
                                                                              
                                                                                 
           
                                                          
                                                   
                                                                                               
                                                                
                                                                        
                                                                
                       
                                         
                                                                                     
                                                                
                                  
                                  
          


                                                                       
                               
                                                                                                  

                                                                
                                       
                                                                                           
                   
                                                                                           

                                                                             
                                                                                      
                                                                   
                                                         
                                                              
                                              
                                                                           
                                                            
                                                               
                                                                                               
                                                                                       
                                                        
                                                                              
                                                              
           
                                                          
                                                   
                                                                                               
                                                                
                                                                        
                                                                
                       
                                                           
                                                                               
                                                                
                                  
                                  
          

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular volume

lemma measurable_torusLift_borel {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] (h : Pt 2 → β) (hc : Continuous h) : Measurable (torusLift h) :=
  hc.measurable.comp (Measurable.of_eval fun i => measurable_circRep.comp (measurable_pi_apply i))

/-- Pushing the uniform law of `𝕋²` forward along a periodic function is unchanged by composing
with a map of `ℝ²` that descends to a measure-preserving map of `𝕋²`. -/
lemma map_cell_comp_of_torus {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (g : Pt 2 → β) (hg : Continuous g) (hp : IsPeriodic g) (T : Pt 2 → Pt 2)
    (τ : UnitAddTorus (Fin 2) → UnitAddTorus (Fin 2)) (hτ : MeasurePreserving τ volume volume)
    (hT : ∀ z, torusProj (T z) = τ (torusProj z)) :
    ((volume : Measure (Pt 2)).restrict (cell 2)).map (fun z => g (T z)) =
      ((volume : Measure (Pt 2)).restrict (cell 2)).map g := by
  have hm := measurable_torusLift_borel g hg
  have hproj := measurePreserving_torusProj
  have e1 : (fun z => g (T z)) = (torusLift g ∘ τ) ∘ torusProj := by
    funext z; simp [hT, ← torusLift_proj g hp (T z)]
  have e2 : g = torusLift g ∘ torusProj := by
    funext z; simp [torusLift_proj g hp z]
  rw [e1, ← Measure.map_map (hm.comp hτ.measurable) hproj.measurable, hproj.map_eq,
    ← Measure.map_map hm hτ.measurable, hτ.map_eq]
  conv_rhs => rw [e2, ← Measure.map_map hm hproj.measurable, hproj.map_eq]

/-- The law of `g(x - Z)` for `Z` uniform on `𝕋²` is the law of `g(Z)`. -/
lemma map_cell_sub_left {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (g : Pt 2 → β) (hg : Continuous g) (hp : IsPeriodic g) (x : Pt 2) :
    ((volume : Measure (Pt 2)).restrict (cell 2)).map (fun z => g (x - z)) =
      ((volume : Measure (Pt 2)).restrict (cell 2)).map g := by
  refine map_cell_comp_of_torus g hg hp (fun z => x - z) (fun u i => torusProj x i - u i) ?_ ?_
  · exact measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun i => Measure.measurePreserving_sub_left volume (torusProj x i)
  · intro z; funext i; simp [torusProj]

                                                                                     
                                                                                          
                                                                       
                                                                                            
                                                               
                                                  
                                                                                     
                                                                          
                                                                    
                                                                                         
                                                                                 
                         
                                                                                     
                                                                               
                                                                                               
                                  
                          
                
                                                           
                                                          

end TorusParseval

end AnomDiss
