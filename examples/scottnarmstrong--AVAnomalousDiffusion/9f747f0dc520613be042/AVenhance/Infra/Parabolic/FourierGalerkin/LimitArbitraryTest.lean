-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.LimitWeakEquation
public import AVenhance.Infra.Parabolic.FourierGalerkin.LimitRepresentation
public import Mathlib

/-!
# Arbitrary tests for the synchronized Galerkin limit

The finite Fourier cutoff weak identity passes to every spacetime test by the spacetime
`L²` tail estimates and the Cauchy--Schwarz inequality on the physical cell.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance arbitraryTestMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance arbitraryTestMeasureIsAddHaar : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance arbitraryTestProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance arbitraryTestProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance arbitraryTestTopHolderTwo : (⊤ : ENNReal).HolderTriple 2 2 :=
  ENNReal.HolderTriple.symm
local instance arbitraryTestFiniteUnitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]
def LimitArbitraryTest.arbitraryTestClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

                                                                      
                                                      

theorem LimitArbitraryTest.arbitraryTest_unitCube_measurable : MeasurableSet AVenhance.unitCube := by
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem LimitArbitraryTest.arbitraryTest_timeCube_measurable : MeasurableSet AVenhance.timeCube := by
  rw [AVenhance.timeCube]
  exact measurableSet_Ioo.prod LimitArbitraryTest.arbitraryTest_unitCube_measurable

theorem LimitArbitraryTest.arbitraryTestClosedCell_compact : IsCompact LimitArbitraryTest.arbitraryTestClosedCell := by
  simpa [LimitArbitraryTest.arbitraryTestClosedCell] using
    isCompact_Icc.prod (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

                                                                   
                                                                     
                                                                 
                                                    

                                                                           
                                                                                
            
                                                                                   
                                                       
         
                  
                                        

theorem LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell :
    AVenhance.timeCube ⊆ LimitArbitraryTest.arbitraryTestClosedCell := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  have hxi := hx i (Set.mem_univ _)
  exact ⟨le_of_lt hxi.1, le_of_lt hxi.2⟩

                                                                                 
                         
                                                        
                                                      
                                                
                                                                                                                     
                                                                
                                                                   

                                                                           
                                                            
                                                               
                                                    
                                                                         
                                                                       

                                                                                
                                                                         
                                                                     
                                                   
                                            
                                                                       
                                                             
                                                     
                
       
             
                       

                                                                   
                       
                                                               
                                                             
                        
                                                                                    
                                                                       
                                         
                                                                             
           
                                                                          
                                     
                                                                              
                                                
                                                               
                                                                                        
                                    
                                         
                                                                
                   
           
                                                   
                                             
                                            
                                                                      
                                    
                                         
                                                                             
                                                                                  
                      
           
                                                                           
                                                  
        
                                                                           
                                                                                 
                                                         
                                                                                  
                   
              
                                                                              
             
                                                                    
                                                       
      
                                                
                                           
                                                   
                                                                          
                                                                       
                                                    
                                                                    
                  
                                           
                                                                                  
                                  
                  
                                                  
           
                                           
                                                                                   
                                  
                  
                             
                                            
                                                                               
                                                         

theorem LimitArbitraryTest.timeCube_measure_eq_iterated :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict,
    ← Measure.volume_eq_prod ℝ (Vec 2)]

local instance arbitraryTestFiniteTimeCube :
    IsFiniteMeasure (volume.restrict AVenhance.timeCube) := by
  rw [LimitArbitraryTest.timeCube_measure_eq_iterated]
  infer_instance

theorem LimitArbitraryTest.galTime_eq_Ioo_measure :
    GalerkinTimeMeasure = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
  change volume.restrict (Set.Ioc (0 : ℝ) 1) = _
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc).symm

                                                                                  
                         
                                          
                                                                            
                                                       
                                                
                                                                                                                     
                                                                
                                                           
                                                 
                                                   
                                                          
              
                                                      
      
                                                              
                                              
                                          
                                               
                                                      
                                          
                                                   
                                    
                                                          
               

                                                                                         
                                 
                                           
                         
                                                                     
                                                                           
                                                               
                                                                               
                                               
                                               
                                                               
                                                                                               
                      
                                                                                 

                                                                                                
                               
                                                              
                                                                  

                                                                              
                                                           
                                                                         
                                                             

theorem LimitArbitraryTest.arbitraryTest_spacetimeGradient_continuous
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => AVenhance.spaceGrad (φ p.1) p.2) := by
  apply continuous_pi
  intro i
  have hFderiv : Continuous
      (fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2)) :=
    hφ.continuous_fderiv (by norm_num)
  have h : Continuous (fun p : ℝ × Vec 2 =>
      (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p)
        (0, Homogenization.basisVec i)) :=
    hFderiv.clm_apply continuous_const
  have heq (p : ℝ × Vec 2) :
      AVenhance.spaceGrad (φ p.1) p.2 i =
        (fderiv ℝ (fun q : ℝ × Vec 2 => φ q.1 q.2) p)
          (0, Homogenization.basisVec i) := by
    let F : ℝ × Vec 2 → ℝ := fun q => φ q.1 q.2
    have houter : HasFDerivAt F (fderiv ℝ F (p.1, p.2)) (p.1, p.2) :=
      (hφ.differentiable (by norm_num) (p.1, p.2)).hasFDerivAt
    have hline : HasFDerivAt (fun x : Vec 2 => (p.1, x))
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hcomp := HasFDerivAt.comp p.2 houter hline
    have hlineEval : (ContinuousLinearMap.inr ℝ ℝ (Vec 2))
        (Homogenization.basisVec i) = (0, Homogenization.basisVec i) := by
      simp [ContinuousLinearMap.inr]
    change fderiv ℝ (F ∘ fun x : Vec 2 => (p.1, x)) p.2
        (Homogenization.basisVec i) = _
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, hlineEval]
    rfl
  exact h.congr fun p => (heq p).symm

                                                           
                                                         
                                                                      
                                                         
                                                
                                                                                  
                                                                           
                                                                         
                                                                          
                                                
                                                                                 
                                                           
                                                        
                                                                         
                                                                                                                     
                                                                       
                                                
                                                                                            
            
                                                             
                                                                
                                                        

theorem LimitArbitraryTest.arbitraryTest_timeCube_vectorEnergy_eq
    {F : ℝ × Vec 2 → Vec 2} (hF : Continuous F) :
    (∫ p in AVenhance.timeCube, Homogenization.vecNormSq (F p)) =
      ∫ t, AVenhance.gradNormSq (fun x => F (t, x)) ∂GalerkinTimeMeasure := by
  have hsq : Continuous (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (F p)) := by
    unfold Homogenization.vecNormSq Homogenization.vecDot
    exact continuous_finsetSum Finset.univ fun i hi =>
      ((continuous_apply i).comp hF).mul ((continuous_apply i).comp hF)
  have hInt : Integrable (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (F p))
      (volume.restrict AVenhance.timeCube) := by
    exact hsq.continuousOn.integrableOn_compact LimitArbitraryTest.arbitraryTestClosedCell_compact |>.mono_set
      LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
  have hIntProd : Integrable (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (F p))
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube)) := by
    rw [← LimitArbitraryTest.timeCube_measure_eq_iterated]
    exact hInt
  rw [LimitArbitraryTest.timeCube_measure_eq_iterated]
  calc
    (∫ p, Homogenization.vecNormSq (F p) ∂
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict AVenhance.unitCube))) =
      ∫ t : ℝ, ∫ x : Vec 2, Homogenization.vecNormSq (F (t, x))
        ∂(volume.restrict AVenhance.unitCube)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := integral_prod _ hIntProd
    _ = ∫ t, AVenhance.gradNormSq (fun x => F (t, x))
        ∂GalerkinTimeMeasure := by rw [LimitArbitraryTest.galTime_eq_Ioo_measure]; rfl

                                                              
                                          
                                                
                                                
                                   
                                                                     
              
                           
                                                          
                                                    
                                        
                                          
                                                
                                                               
                                   
                                     
                           
                                    
                               
                                                                                           
                         
                                                      
                                                                  
                                       

                                                                
                                                          
                               
                                         
                                                         
                                                
                                                      
                                                                       
                                             
                                                                    
                                                             
                   
                            
                                                                         
                
                                                                          
                                                                     
                                   
                                                                       
               
                                                                          
                                             
                                                  
                                                            
                         
                                                   
                                   

                                                                     
                       
                                                               
                                                     
                                                
                                              
                                                  
                                                         
                       
                                                    
                                                                                     
                                                  
                                                      
                                             
                                                  
                                                          
                                                                          
                                            
                                                                                       
                    
                                 
                                                
                                                    
                                                             
                                       
                                           
                                                    
                                                                             
                                    
                                                                     
                                

                                                                      
                       
                                                               
                                                     
                                                
                  
                                                                      
                       
                                                      
                                                                                 
                                                                       
                                           
                                                                              
                    
                                 
                    
                                                                          
                                       
                                                                     
                                    
                                                                                                    
                                

theorem LimitArbitraryTest.arbitraryTest_gradientCutoffCoordError_l2Sq_tendsto
    {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hperiodic : ∀ t, AVenhance.IsZ2Periodic (φ t)) (i : Fin 2) :
    Tendsto (fun N => ∫ p in AVenhance.timeCube,
      (AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2)
      atTop (𝓝 0) := by
  have hφone : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => φ p.1 p.2) :=
    hφ.of_le (by norm_num)
  have hcutone (N : ℕ) : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 =>
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) :=
    (spacetimeTestFourierCutoff_contDiff_top hφ hperiodic N).of_le (by norm_num)
  have herrOne (N : ℕ) : ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => φ p.1 p.2 -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N p.2) :=
    hφone.sub (hcutone N)
  let η (N : ℕ) : ℝ → Vec 2 → ℝ := fun t x =>
    φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x
  have hηone (N : ℕ) : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => η N p.1 p.2) := by
    simpa [η] using herrOne N
  have hgradCont (N : ℕ) : Continuous (fun p : ℝ × Vec 2 =>
      AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2) := by
    simpa [η] using LimitArbitraryTest.arbitraryTest_spacetimeGradient_continuous (φ := η N) (hηone N)
  have hcoordEnergy (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2) ≤
      ∫ p in AVenhance.timeCube,
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2) := by
    have hcoordInt : Integrable (fun p : ℝ × Vec 2 =>
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2)
        (volume.restrict AVenhance.timeCube) := by
      have hcont : Continuous (fun p : ℝ × Vec 2 =>
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2) :=
        (((continuous_apply i).comp (hgradCont N)).pow 2)
      exact (hcont.continuousOn.integrableOn_compact LimitArbitraryTest.arbitraryTestClosedCell_compact).mono_set
        LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
    have hvecInt : Integrable (fun p : ℝ × Vec 2 =>
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2))
        (volume.restrict AVenhance.timeCube) := by
      have hsq : Continuous (fun p : ℝ × Vec 2 =>
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (fun x => φ p.1 x -
              AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2)) := by
        unfold Homogenization.vecNormSq Homogenization.vecDot
        exact continuous_finsetSum Finset.univ (fun j hj =>
          ((continuous_apply j).comp (hgradCont N)).mul
            ((continuous_apply j).comp (hgradCont N)))
      exact (hsq.continuousOn.integrableOn_compact LimitArbitraryTest.arbitraryTestClosedCell_compact).mono_set
        LimitArbitraryTest.timeCube_subset_arbitraryTestClosedCell
    apply setIntegral_mono_on hcoordInt hvecInt LimitArbitraryTest.arbitraryTest_timeCube_measurable
    intro p hp
    simp only [Homogenization.vecNormSq, Homogenization.vecDot]
    simpa [pow_two] using (Finset.single_le_sum (s := Finset.univ)
      (fun j hj => sq_nonneg
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 j))
      (Finset.mem_univ i))
  have hvector := spacetimeTestGradientCutoff_error_integral_tendsto hφ hperiodic
  have hvectorEq (N : ℕ) :
      (∫ p in AVenhance.timeCube,
        Homogenization.vecNormSq
          (AVenhance.spaceGrad (fun x => φ p.1 x -
            AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2)) =
      ∫ t, AVenhance.gradNormSq (AVenhance.spaceGrad (fun x =>
        φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x))
          ∂GalerkinTimeMeasure := by
    simpa [AVenhance.gradNormSq] using LimitArbitraryTest.arbitraryTest_timeCube_vectorEnergy_eq
      (hgradCont N)
  have hbound : ∀ᶠ N in atTop,
      ∫ p in AVenhance.timeCube,
        (AVenhance.spaceGrad (fun x => φ p.1 x -
          AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2 ≤
        ∫ t, AVenhance.gradNormSq (AVenhance.spaceGrad (fun x =>
          φ t x - AVenhance.Infra.Section5.testFourierCutoff (φ t) N x))
            ∂GalerkinTimeMeasure := by
    filter_upwards with N
    exact (hcoordEnergy N).trans_eq (hvectorEq N)
  have hnonneg : ∀ N, 0 ≤ ∫ p in AVenhance.timeCube,
      (AVenhance.spaceGrad (fun x => φ p.1 x -
        AVenhance.Infra.Section5.testFourierCutoff (φ p.1) N x) p.2 i) ^ 2 := by
    intro N
    exact setIntegral_nonneg LimitArbitraryTest.arbitraryTest_timeCube_measurable
      (fun p hp => sq_nonneg _)
  exact squeeze_zero' (Eventually.of_forall hnonneg) hbound (by simpa [hvectorEq] using hvector)

                                                                   
                       
                                                         
                           
                                
                                                                      
                    
                                                                               
                                                             
                                 
                                                      
                                                                           
                                                                                
                               
                                                                 
                                                                               
                         
                                                              
                                                                    
                                         
                                          

                                                                        
                                                                 
                       
                                                                                   
                                                                        

                                                      
                                                                   
                                              
                                                                      
            
                                 
                    
                                                        
                                                         
                            

                                                                      
                                                
                                                               
                                                     
                     
                                         
                                                 
                                                           
                                                                 
                                                                            
                                                                             
                                   
                                         
                                                             
                                                                 
                                           
                        
                                          
                                                 
                                                             
                              
                             
                                                                                      
                                                                              
        
                                          
                                                 
                                                             
                                           
                                  
                                                                                   
                                     
                                  
                                              
                                                                                  
                              
                                  
                               
                                                                                        
                                                                                
                                                                                             
                      
                              
                             
                                                                                      
                                                                          
                                         
                                                                  
                                            
                                                                                  
                                                                   
                                            

                                                                     
                                                 
                             
                                                  
                                                    
                                                                   
                                                                   
                                                                                  
                                              
                                      
                                                          
                                                                
                                                      
            
                                
                  

                                                                          
                                                            
                                       
                                                                 
                                                                               
                            
                                                                                 
                            
                                          
                                             
                                                         
                       
                                                               
                                                   
                                               
                              
                                                              
                                        
                                           
                                                                          
                                   
                                                            
                                              
                                                     
           
                                                                     
                                                                                        
                                                                              
                                                         
                                                  
                                                      
                                                 
                                                       
                                                                                
                                                                                 
                                                     
                                                                 
                                         
                                                  
                                                                         
                                                 
                                                          
                                 
                                                                                  
                                                    
                                                      
                                                     
                                                                   
                                                            
                                                                      
                           
                                                                    
                                                                                
                               
                                                                                           
                                                            
                                                        
                                                                            
                                                               
                          
                                                                                    
                                                                       
                                                          
                                                  
                                                                                         
                                                                     
                                        
                                                                                       
                                                      
                                                             
                                           
                                                          
                                  
                                                            
                                      
                                   
                                                                 
                          
                                                       
                            
                                                                      
                                               
                                                   
                                       
                                                          
                                                              
                                                                 
                             
                                                                                                      
                                                                                          
                                                                                              
                             
                                                                                         
                                                                                                             
                                                                                                                    
                                                                                           
                                     
                                                                     
                                                              
                                                             
                                                            
                                                                
                                    
                                                                     
                                                                                            
                                      
                                                      
                                                                           
                                                                                         
                                              
                                            
                                                                     
                                       
                                                                                       
                                                               
                                                  
                                                                             
                                        
              
                           
            
                        
                                        
                                                                           
                                       
                                                                 
                               
                                                                                    
                                                                                             
                                
                                                                         
                                                                           
                                   
                                                      
                                                                           
                                              
                                                                              
                                                                                                      
                                              
                                                                                               
                                                                                         
                                                                           
                                    
                                                                  
                                     
                                                   
                                                             
              
                    
                    
                                                       
                                                                                                      
                                                                                                    
                                                                          
                     
                                    
                                     
                                                               
                                              
                                                   
                                                                        
              
                    
                    
                                                          
                                                                                   
                                                                                   
                                                                                   
                                                                               
                                            
                                                                                                         
                                    
                                                                   
                                        
                                                                                        
              
                       
                    
                                         
                                                     
                                                      
                                          
                                                               
                                                        
                              
                                                         
                              
                                                                        
                                                 
                                                     
                                                                                     
                                                                               
                                         
                                           
                                       
                                                                    
                     
         
        
                                             
                                                    
                                                                                    
                                                                                
                                                         
                         
                                  
          
                                     
                                   
                                
        
                        
                                              
                                                  
                                                           
        
                                              
                                                                       
                                   
                                 
                                  
                                                    
                                                          
                                              
                                            
                                                                  
                                                                           
                                                                                                          
                             
                                                   
                                                               
                                                            
                            
                                                                  
                                                                                     
                                                                              
                                                                                      
                                                                               
                                                                                               
                                                                     
                                                     
                                                                                     
                                                         
              
                                  
                                                 
                                           
                           
                                                      
                                                                
                                               
                                 
                                                            
                                                              
                            
                                   
                                                               
                                             
                                                                            
                                     
                                                                
                                                  
                                       
                                                                    
                                               
                            
                                   
                                                              
                                                
                                                                   
                                                                
                                    
                          
                                                                                
                                                                             
                  
                                                                            
        
                                                   
                                    
                                                                 
                                               
                                                                                 
                                       
                                     
                                 
                                     
                                                                
                                                  
                                       
                                                                 
                                 
                                      
                                           
                                                               
                                             
                                                              
                                                                        
                                                                  
                                                               
                              
                                                                    
                                                  
                           
                                                                   
                       
                                             
                            
                                                               
                       
                                        
                                       
                                                                 
                       
                                           
                             
                            
                                                                           
                                                  
                                        
                                                                 
                                       
                                               
                                                       
                                    
                                                                 
                                                                         
                      
                                                  
                                                  
                                                             
                          
                                                        
                        
                                                
                                           
                                                   
                                                                  
                                                 
                                                                         
                                                               
                                                                                                
                                          
                                         
                                                 
                                                                 
                                                                 
                                                                                 
                                                                 
                                                                          
                                                    
                                                   
                                                                  
                           
                     
                                                        
                                                      

end AVenhance.Infra.Parabolic.FourierGalerkin

end
