-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjection
public import AVenhance.Infra.Heat.WeakBridge
public import AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import Mathlib

/-!
# Strong convergence of weak Fourier cutoffs

The finite real Fourier cutoffs of a weak path converge in spacetime `L²`, together with
their spatial gradients. This is the strong convergence needed to pass the finite coefficient
energy balances to the weak path.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.WeakUniqueness

open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical

local instance weakProjectionConvergenceMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakProjectionConvergenceMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakProjectionConvergenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance weakProjectionConvergenceProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

theorem weakProjection_scalarTransfer_normSq {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    ‖(weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f)‖ ^ 2 = AVenhance.l2NormSq f := by
  rw [l2_norm_sq_eq_integral_sq]
  calc
    ∫ x : Torus, ‖(weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f) x‖ ^ 2 =
        ∫ x : Torus, ‖AVenhance.Infra.Torus.periodicToTorus f x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [(weakProjection_realCellToTorus_memLp hf).coeFn_toLp] with x hx
          rw [hx]
    _ = ∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus
        (fun y => f y ^ 2) x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [AVenhance.Infra.Torus.periodicToTorus, Real.norm_eq_abs, sq_abs]
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, f x ^ 2 :=
      AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell _
    _ = AVenhance.l2NormSq f := by
      rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
      rfl

theorem WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
    {u : ℝ → Vec 2 → ℝ} {t : ℝ} {N : ℕ}
    :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus (u t)) =
    weakFourierCoefficientPath N u t := by
  ext i
  let a := (realFourierIndexEquivFin N).symm i
  change (∫ x : Torus,
      AVenhance.Infra.Torus.periodicToTorus (u t) x * realFourierModeFin N i x) = _
  rw [realFourierModeFin_eq_periodicToTorus]
  change (∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus
      (fun y => u t y * realFourierModeAmbient N a y) x) = _
  rw [AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell,
    AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  simp [weakFourierCoefficientPath, weakModePairing, a]

theorem WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing
    {f : Vec 2 → ℝ} (hf : MemL2On AVenhance.unitCube f) (N : ℕ) :
    realFourierProjectionCoefficients N
        ((weakProjection_realCellToTorus_memLp hf).toLp
          (AVenhance.Infra.Torus.periodicToTorus f)) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus f) := by
  ext i
  unfold realFourierProjectionCoefficients modeProjectionCoefficients
  change (∫ x : Torus,
      ((weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f)) x * realFourierModeFin N i x) = _
  apply integral_congr_ae
  filter_upwards [(weakProjection_realCellToTorus_memLp hf).coeFn_toLp] with x hx
  rw [hx]

                                                                                          
                                                                              
                                                                                          
                                                
                                              
                                                   
                                                     
                                                         
                                     
                             
                                                                           
                                            
               
                                                                           
                                                      
                                                       
                                              
                                  
                  
                             
                                                       
                                                         
                  
                                                          
                                          
               
        
                                                                              
                                                                             
                                   
      
  

                                                                                  
                                                        
                                                                       
                                                                              
                                                                   
                                                                                      
                                                                     
                                                                                                        
                   

                                                                                              
                                       
noncomputable def weakFourierProjectionL2 (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    ScalarTorusL2 :=
  realFourierScalarMap N (weakFourierCoefficientPath N u t)

                                                                                   
                                                                       
                          
                                                                      

                                                                  
                                                                             
                                          
                        
                                                                                  

                                                                                         
                                                 
                                                                                 
                                                                           
          
                                                   
                                                                    
                                                                
                            
            
                                            
     

                                                                                   
                                                 
                              
                                           
                                                                                                 
                                                                                           
                                     
                                                             
                                                       
              
                                  
                                                   
                                                                                           

                                                    
                                         
                                   
                                           
                                                                            
                                                               
                                                                                       
                                                                                                                

                                                            
                                                     
                                             
                                           
                                
             
                                                                 
                                                
                                               
                                                         
                                                                                  
                                                                                     
                                              
                                                                                     
                                           
                                                       
                                                                                      
                                                                        
                                               
                                                                          
                                       
                                                                                   
                                                                          
                                             
                                            
                                                                                         
                                     
                                                                                       
                                                                                      
      
                               
                                                             
                                                                                           
                                                                              
                                                            
                                                
                                                                                           
                  
                                                                                  
                                                                                       
                        
                                       

                                                                              
                                                   
                                                
                                                          
                                          
                                                                             
                                                                
                                                         
                                                
                             
                                          
                                           
                                                                       
                                                       
                                                                                
                                                                 
                                                                      
                                                        
                                                         
                                           
                
                                                                            
                                                               
                                                           
                                                                      
                                                      
                                                                   
                                                   
                                                      
                                                         
                                                
                                                          
                                                                       
                                                
                                                       
                          
                     
                            
                 
                                                
                                                          
      
                                               
                                                          
                                                                                
                
                                                           
                                                         
                                                            

                                                                                                  
                                                                                
                                                        
                                                                       
                                           
                                                                  
                                                                
                                                                     
                                                          
                           
                                          
                                                                                
                                                         
                                        
                                       
                                                 
                                                                          
                                                                     
                                                                              
                                     
                                        
                                                                      
                                                                 
                                            
                                                          
                                                        
                                                                       
                                                     
                
                                                                            
                                                               
                                                           
                                                                      
                                                                    
                                                                             
                                                             
                                                      
                                                
                                                       
                                                
                                                                    
                                                                       
                                                          
                                             
                                                      
                          
                     
                            
                 
                                                
                                                          
      
                                                                        
                                                          
                                                
                                                                               
                                                           
                                                                       
                                                                      

                                                                                  
                                                   
                                                
                                                          
                                          
                                                                             
                                                                          
                           
                                                           
                                                 
                                                       
                                            
                                                                                       
                                                                               
                                                        
                                                         
                                                                                                          
      
                                                                             
                                                  
                                                                                    
                                                              
                                                                            
                                                    

                                                                                    
                                                        
                                                                       
                                           
                                                                  
                                              
                                                           
                         
                                                           
                                                               
                                                       
                                                                                        
                                                                                       
                                                                                          
                                                                  
                                                                   
                                                                                                                  
      
                                           
                                                                    
                                                            
                                                                                    
                                                                        
                                                
                                                             
                                                    

                                                                                      
theorem weakFourierProjectionL2_tendsto
    {u : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hu : MemL2On AVenhance.unitCube (u t)) :
    Tendsto (fun N => weakFourierProjectionL2 N u t) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp hu).toLp
        (AVenhance.Infra.Torus.periodicToTorus (u t)))) := by
  let v := (weakProjection_realCellToTorus_memLp hu).toLp
    (AVenhance.Infra.Torus.periodicToTorus (u t))
  have hcoeff : ∀ N, realFourierProjectionCoefficients N v =
      weakFourierCoefficientPath N u t := by
    intro N
    rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing hu]
    exact WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
  have hsequence : (fun N => weakFourierProjectionL2 N u t) =
      fun N => realFourierScalarMap N (realFourierProjectionCoefficients N v) := by
    funext N
    simp [weakFourierProjectionL2, hcoeff N]
  rw [hsequence]
  exact tendsto_realFourierProjection v

                                                                                        
                                                                   
                                               
                                                        
                                                               
                                            
                                                                                       
                                                                         
                                                                           
                                                                    
                                                               
                                                            
                                                                                        
           
                                                                                                
                                                                                          
                                                   
                                                                                       
                                                                                   
            
                   
                
                                       

theorem WeakProjectionConvergence.weakFourierMode_smooth (N : ℕ) (i : Fin (RealFourierDimension N)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  (realFourierModeAmbient_contDiff N
    ((realFourierIndexEquivFin N).symm i)).of_le (by simp)

theorem WeakProjectionConvergence.weakFourierMode_periodic (N : ℕ) (i : Fin (RealFourierDimension N)) :
    AVenhance.IsZ2Periodic
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i)

theorem WeakProjectionConvergence.weakFourierCoefficientPath_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) :
    ContinuousOn (fun t => weakFourierCoefficientPath N u t)
      (Set.Icc (0 : ℝ) 1) := by
  let g : ℝ → Fin (RealFourierDimension N) → ℝ := fun t i =>
    weakModePairing u
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_pi.2
    intro i
    exact hu.2.2.2.2.2.2.1
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i))
      (WeakProjectionConvergence.weakFourierMode_smooth N i) (WeakProjectionConvergence.weakFourierMode_periodic N i)
  have htoLp : Continuous (WithLp.toLp 2 :
      (Fin (RealFourierDimension N) → ℝ) → Coefficients (RealFourierDimension N)) :=
    PiLp.continuous_toLp 2 (fun _ : Fin (RealFourierDimension N) => ℝ)
  have hcomp := htoLp.continuousOn.comp hg (fun _ _ => Set.mem_univ _)
  convert hcomp using 1
  funext t
  rfl

theorem weakFourierProjectionL2_normSq_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N => ‖weakFourierProjectionL2 N u t‖ ^ 2) atTop
      (𝓝 (AVenhance.l2NormSq (u t))) := by
  have htmem := (hu.1 t ht).2
  have hprojection := weakFourierProjectionL2_tendsto htmem
  have hnorm := (continuous_norm.pow 2).continuousAt.tendsto.comp hprojection
  have hlimit : ‖(weakProjection_realCellToTorus_memLp htmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))‖ ^ 2 =
      AVenhance.l2NormSq (u t) := weakProjection_scalarTransfer_normSq htmem
  change Tendsto (fun N => ‖weakFourierProjectionL2 N u t‖ ^ 2) atTop
    (𝓝 (‖(weakProjection_realCellToTorus_memLp htmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))‖ ^ 2)) at hnorm
  simpa only [hlimit] using hnorm

theorem WeakProjectionConvergence.weakFourierProjectionL2_normSq_continuousOn
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) :
    ContinuousOn (fun t => ‖weakFourierProjectionL2 N u t‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) := by
  have hcoeff := WeakProjectionConvergence.weakFourierCoefficientPath_continuousOn hu N
  have hprojection : ContinuousOn (fun t => weakFourierProjectionL2 N u t)
      (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t => realFourierScalarMap N
      (weakFourierCoefficientPath N u t)) (Set.Icc (0 : ℝ) 1)
    exact (realFourierScalarMap N).continuous.continuousOn.comp hcoeff
      (fun _ _ => Set.mem_univ _)
  exact hprojection.norm.pow 2

                                                                                   
                                                   
                                                
                                                                        
                                                                  
                                                                     
                                                                                   
                                                            
                                    
                                                           
                                                 
                                    
                                                                          
                                                    
                           
           
                                                                         
                                                             
                                                                         
                                                                          
                                                             
                                                                       
                                       
                                       
                                          
                                                                                    
                                                                      
                                                                      
                       
          
                                                 

                                                                                     
                                                   
                                                
                                                                        
                                                                         
                               
                                                                                                   
                                                                                    
                               
                                                        
                                                                                       
                                                                      
                                 
                              

                                                                                
                                                        
                                                               
                                                                          
                                                        
                                                                 
                                                                             
                          
                                                                 
                                                                        
                                                                                         
                                                                               
                                                         
                                                                                 
                                 

                                                                              
                                          
                                                
                                                  
                                                
                                       

                                                                                
                                                   
                                                
                                                                
                                                                
                                                 
                          
                                                                 
                                             
                                                                
                                                                      
                                                 
                                                   
                                                                                
                                           
                                          
                                              
                                                           
            
       
                   
             

                                                                                     
                                                   
                                                
                                                                
                                                                          
                                                 
                                              
                                         
                                                                  
                               
                                 
                                                            
                                                                                              
                                       
                                                                            
                                                                          
                                           
                                                                                                   
                                         

                                                                              
                                                                     
                                                   
                                                
                                                                
                                               
                                              
                                                      
                       
                                              
                                 
                                            
                                                   
                                                          
                                                                                                  
                                                            
                                                                                              
                                       
                                                              
                                                                               
                                                                                 
                                          
                                                  
                                           
                             
                                                             
                                                                 
                                                                     
                                               
                                                         
                                                                                          
                                                                                         
                                                                                             
                                                                             
                                                                           
                                                   
                                                                                                        
                               
                                                                          
                                                                               
                          
                                                                  
                                                    
                   
                                                                   
                                                                       
                   
                
                                                    
                                                        
                    
                             
                                                                   
                                           
                                                                                               
                                                                               
                                                                                
                                    
                                                        
                                                                               
                         

theorem WeakProjectionConvergence.weakFourierProjectionL2_normSq_aestronglyMeasurable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) (N : ℕ) :
    AEStronglyMeasurable (fun t => ‖weakFourierProjectionL2 N u t‖ ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  exact ContinuousOn.aestronglyMeasurable_of_subset_isCompact
    (WeakProjectionConvergence.weakFourierProjectionL2_normSq_continuousOn hu N) isCompact_Icc measurableSet_Ioo
    (by intro t ht; exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-- The full scalar slice norm is measurable because it is the pointwise limit of the continuous
finite Fourier coefficient norms. -/
theorem WeakProjectionConvergence.weakPath_l2NormSq_aestronglyMeasurable
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) :
    AEStronglyMeasurable (fun t => AVenhance.l2NormSq (u t))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let G : ℝ → ℝ := fun t => Filter.limsup
    (fun N => ‖weakFourierProjectionL2 N u t‖ ^ 2) atTop
  have hG : AEMeasurable G μ :=
    AEMeasurable.limsup (fun N =>
      (WeakProjectionConvergence.weakFourierProjectionL2_normSq_aestronglyMeasurable hu N).aemeasurable)
  have hEq : G =ᵐ[μ] fun t => AVenhance.l2NormSq (u t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (weakFourierProjectionL2_normSq_tendsto hu t
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩).limsup_eq
  exact hG.aestronglyMeasurable.congr hEq

/-- The scalar Fourier projection errors converge strongly in time `L²`. The equality with the
cell error is the Pythagorean identity for the finite orthogonal projection. -/
theorem weakFourierProjection_scalarL2_time_integral_tendsto
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u Du) :
    Tendsto (fun N => ∫ t in Set.Ioo (0 : ℝ) 1,
      AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2)
      atTop (𝓝 0) := by
  let μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let e : ℕ → ℝ → ℝ := fun N t =>
    AVenhance.l2NormSq (u t) - ‖weakFourierProjectionL2 N u t‖ ^ 2
  have heMeas (N : ℕ) : AEStronglyMeasurable (e N) μ := by
    exact (WeakProjectionConvergence.weakPath_l2NormSq_aestronglyMeasurable hu).sub
      (WeakProjectionConvergence.weakFourierProjectionL2_normSq_aestronglyMeasurable hu N)
  obtain ⟨C, hC⟩ := hu.2.1
  have hCnonneg : 0 ≤ C := by
    have hzero := hC 0 ⟨le_rfl, by norm_num⟩
    have hmem := (hu.1 0 ⟨le_rfl, by norm_num⟩).2
    rw [← weakProjection_scalarTransfer_normSq hmem] at hzero
    exact le_trans (sq_nonneg ‖(weakProjection_realCellToTorus_memLp hmem).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u 0))‖) hzero
  have hbound (N : ℕ) : ∀ᵐ t ∂μ, ‖e N t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    let v := (weakProjection_realCellToTorus_memLp (hu.1 t htcc).2).toLp
      (AVenhance.Infra.Torus.periodicToTorus (u t))
    have hnormv : ‖v‖ ^ 2 = AVenhance.l2NormSq (u t) :=
      weakProjection_scalarTransfer_normSq (hu.1 t htcc).2
    have hprojcoeff : realFourierProjectionCoefficients N v =
        weakFourierCoefficientPath N u t := by
      rw [WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing (hu.1 t htcc).2]
      exact WeakProjectionConvergence.weakProjection_scalarCoefficient_eq_pairing
    have hcoeffcontract : ‖realFourierProjectionCoefficients N v‖ ≤ ‖v‖ := by
      have hcoeff := realFourierModeFin_projectionCoefficients_norm_le N
        (weakProjection_realCellToTorus_memLp (hu.1 t htcc).2)
      rw [← WeakProjectionConvergence.weakProjection_scalarL2_coefficients_eq_pairing (hu.1 t htcc).2] at hcoeff
      simpa [v] using hcoeff
    have hcontract : ‖weakFourierProjectionL2 N u t‖ ≤ ‖v‖ := by
      rw [weakFourierProjectionL2, ← hprojcoeff, realFourierScalarMap_norm]
      exact hcoeffcontract
    have hprojSq : ‖weakFourierProjectionL2 N u t‖ ^ 2 ≤
        AVenhance.l2NormSq (u t) := by
      rw [← hnormv]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcontract
    have hfull : AVenhance.l2NormSq (u t) ≤ C := hC t htcc
    have hfullNonneg : 0 ≤ AVenhance.l2NormSq (u t) := by
      rw [← hnormv]
      positivity
    have herror : |e N t| ≤ C := by
      change |AVenhance.l2NormSq (u t) -
        ‖weakFourierProjectionL2 N u t‖ ^ 2| ≤ C
      apply abs_le.mpr
      constructor <;> nlinarith
    simpa [Real.norm_eq_abs] using herror
  have hdom : Integrable (fun _ : ℝ => C) μ := by
    have hs : volume (Set.Ioo (0 : ℝ) 1) ≠ (⊤ : ENNReal) := by
      rw [Real.volume_Ioo]
      norm_num
    exact integrableOn_const (μ := volume) (s := Set.Ioo (0 : ℝ) 1)
      (C := C) hs (by simp)
  have hpoint : ∀ᵐ t ∂μ, Tendsto (fun N => e N t) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hnorm := weakFourierProjectionL2_normSq_tendsto hu t htcc
    have hconst : Tendsto (fun _ : ℕ => AVenhance.l2NormSq (u t)) atTop
        (𝓝 (AVenhance.l2NormSq (u t))) := tendsto_const_nhds
    simpa [e] using hconst.sub hnorm
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => C) heMeas hdom hbound hpoint
  simpa [e, μ] using hDCT

                                                                       
                                                                                             
                                                   
                                                
                                                    
                                               
                                                                              
                       
                                                                        
                                                 
                          
                                                                         
                                        
                                                                            
                         
                           
                                                                
                                                                                         
                                    
                               

                                                                                             
                                                                                               
                                                   
                                                
                                                                
                                               
                                             
                                                                   
                       
                                                                                   
                                                 
                                               
                                                                               
                                        
                                                
                                                             
                         
                           
                                           
                                                                                             
                               

                                                                                
                                                                                                
           
                                                        
                                                   
                                                
                                                    
                     
                                
                          
                                                                 
                                            
                                               
                                                                     
                       
                                                                                                         
                                                                           
                                               
                                                                     
                                            
                           
              
                                                                                                      
                                  

end AVenhance.Infra.Parabolic.WeakUniqueness

end
