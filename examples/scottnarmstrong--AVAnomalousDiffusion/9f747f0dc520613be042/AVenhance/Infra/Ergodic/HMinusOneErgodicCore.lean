-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Ergodic.HMinusOneSpectral
public import AVenhance.Infra.Ergodic.LatticeDecay
public import Mathlib
/-! # The frequency split in the homogeneous H⁻¹ ergodic estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

variable {d : ℕ} {hd : 0 < d}

local instance avInfraErgodicHMinusOneErgodicCoreMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicHMinusOneErgodicCoreMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicHMinusOneErgodicCoreIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_character (q k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier k) q =
      if q = k then 1 else 0 := by
  have horth := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin d))) q k
  have hcoeff : UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier k) q =
      inner ℂ (UnitAddTorus.mFourierLp 2 q) (UnitAddTorus.mFourierLp 2 k) := by
    simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul,
      UnitAddTorus.mFourier_neg]
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 q,
      UnitAddTorus.coeFn_mFourierLp 2 k] with x hq hk
    simp only [hq, hk, RCLike.inner_apply]
    ring
  rw [hcoeff]
  exact horth

theorem finite_frequencyBall (M : ℕ) :
    {k : Fin d → ℤ | ‖k‖ ≤ (M : ℝ)}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin d => Set.finite_Icc
    (-(M : ℤ)) (M : ℤ))).subset ?_
  intro k hk i
  have hcoord : ‖(k i : ℝ)‖ ≤ (M : ℝ) :=
    (norm_le_pi_norm k i).trans hk
  have habs : |k i| ≤ (M : ℤ) := by
    exact_mod_cast (show (|((k i : ℝ))|) ≤ (M : ℝ) by simpa [Int.norm_eq_abs,
      Int.cast_abs] using hcoord)
  exact (abs_le.mp habs)

def frequencyBall (M : ℕ) : Finset (Fin d → ℤ) :=
  (finite_frequencyBall M).toFinset

theorem mem_frequencyBall {M : ℕ} {k : Fin d → ℤ} :
    k ∈ frequencyBall M ↔ ‖k‖ ≤ (M : ℝ) := by
  simp [frequencyBall]

theorem frequencyBall_neg (M : ℕ) {k : Fin d → ℤ}
    (hk : k ∈ frequencyBall M) : -k ∈ frequencyBall M := by
  rw [mem_frequencyBall] at hk ⊢
  simpa using hk

noncomputable def fourierCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) : C(UnitAddTorus (Fin d), ℂ) :=
  ⟨fun x => ∑ k ∈ frequencyBall M,
    a k * UnitAddTorus.mFourier k x,
    continuous_finsetSum _ fun k hk => by fun_prop⟩

theorem continuous_unitTorus_integrable
    {u : UnitAddTorus (Fin d) → ℂ} (hu : Continuous u) :
    Integrable u (volume : Measure (UnitAddTorus (Fin d))) := by
  have h : IntegrableOn u Set.univ (volume : Measure (UnitAddTorus (Fin d))) :=
    hu.continuousOn.integrableOn_compact (isCompact_univ :
      IsCompact (Set.univ : Set (UnitAddTorus (Fin d))))
  simpa [IntegrableOn] using h

def closedUnitCube : Set (Vec d) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1

theorem unitCell_subset_closedUnitCube :
    Torus.unitCell d ⊆ closedUnitCube := by
  intro x hx
  simp only [closedUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, by simpa using (hx i).2⟩

theorem continuous_complex_unitCell_integrable
    {f : Vec d → ℂ} (hf : Continuous f) :
    IntegrableOn f (Torus.unitCell d) (volume : Measure (Vec d)) := by
  have hcube : IsCompact (closedUnitCube (d := d)) := by
    change IsCompact (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
    exact isCompact_univ_pi fun _ => isCompact_Icc
  exact hf.continuousOn.integrableOn_compact hcube |>.mono_set
    unitCell_subset_closedUnitCube

theorem mFourierCoeff_sum {ι : Type*} (S : Finset ι)
    (F : ι → UnitAddTorus (Fin d) → ℂ) (q : Fin d → ℤ)
    (hF : ∀ k ∈ S, Integrable (fun x =>
      UnitAddTorus.mFourier (-q) x * F k x)
      (volume : Measure (UnitAddTorus (Fin d)))) :
    UnitAddTorus.mFourierCoeff (fun x => ∑ k ∈ S, F k x) q =
      ∑ k ∈ S, UnitAddTorus.mFourierCoeff (F k) q := by
  classical
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ x, UnitAddTorus.mFourier (-q) x * (∑ k ∈ S, F k x)) =
        ∫ x, ∑ k ∈ S, UnitAddTorus.mFourier (-q) x * F k x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
    _ = ∑ k ∈ S, ∫ x,
        UnitAddTorus.mFourier (-q) x * F k x := by
      rw [integral_finsetSum]
      exact hF

theorem mFourierCoeff_const_smul_character (c : ℂ)
    (q k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x => c * UnitAddTorus.mFourier k x) q =
      if q = k then c else 0 := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  rw [show (fun x => UnitAddTorus.mFourier (-q) x *
      (c * UnitAddTorus.mFourier k x)) =
      fun x => c * (UnitAddTorus.mFourier (-q) x *
        UnitAddTorus.mFourier k x) by
          funext x
          ring,
    integral_const_mul]
  change c * UnitAddTorus.mFourierCoeff
      (UnitAddTorus.mFourier k) q = _
  rw [mFourierCoeff_character]
  split_ifs <;> simp_all

theorem mFourierCoeff_fourierCutoff
    (M : ℕ) (a : (Fin d → ℤ) → ℂ) (q : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fourierCutoff M a) q =
      if q ∈ frequencyBall M then a q else 0 := by
  classical
  change UnitAddTorus.mFourierCoeff
    (fun x => ∑ k ∈ frequencyBall M,
      a k * UnitAddTorus.mFourier k x) q = _
  have hF (k : Fin d → ℤ) (hk : k ∈ frequencyBall M) :
      Integrable (fun x => UnitAddTorus.mFourier (-q) x *
        (a k * UnitAddTorus.mFourier k x))
        (volume : Measure (UnitAddTorus (Fin d))) := by
    apply continuous_unitTorus_integrable
    exact (UnitAddTorus.mFourier (-q)).continuous.mul
      (continuous_const.mul (UnitAddTorus.mFourier k).continuous)
  rw [mFourierCoeff_sum (S := frequencyBall M)
    (F := fun k x => a k * UnitAddTorus.mFourier k x) (q := q) hF]
  simp only [mFourierCoeff_const_smul_character]
  simp

theorem fourierCutoff_star_eq (M : ℕ)
    (a : (Fin d → ℤ) → ℂ)
    (ha : ∀ k, a (-k) = star (a k)) (x : UnitAddTorus (Fin d)) :
    star (fourierCutoff M a x) = fourierCutoff M a x := by
  classical
  change star (∑ k ∈ frequencyBall M,
      a k * UnitAddTorus.mFourier k x) =
    ∑ k ∈ frequencyBall M, a k * UnitAddTorus.mFourier k x
  rw [star_sum]
  refine Finset.sum_bij (fun k _ => -k) ?_ ?_ ?_ ?_
  · intro k hk
    exact frequencyBall_neg M hk
  · intro k hk l hl hkl
    exact neg_injective hkl
  · intro k hk
    exact ⟨-k, frequencyBall_neg M hk, by simp⟩
  · intro k hk
    change star (a k * UnitAddTorus.mFourier k x) =
      a (-k) * UnitAddTorus.mFourier (-k) x
    rw [star_mul]
    rw [← ha k, UnitAddTorus.mFourier_neg]
    exact mul_comm _ _

noncomputable def realFourierCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) : C(UnitAddTorus (Fin d), ℝ) :=
  ⟨fun x => (fourierCutoff M a x).re, by fun_prop⟩

theorem realFourierCutoff_complexification (M : ℕ)
    (a : (Fin d → ℤ) → ℂ)
    (ha : ∀ k, a (-k) = star (a k)) :
    (fun x => (realFourierCutoff M a x : ℂ)) = fourierCutoff M a := by
  funext x
  apply Complex.ext
  · rfl
  · have hstar := fourierCutoff_star_eq M a ha x
    have him : (fourierCutoff M a x).im = 0 := by
      have hi := congrArg Complex.im hstar
      simp only [Complex.star_def, Complex.conj_im] at hi
      linarith
    simp [realFourierCutoff, him]

theorem smoothFourierCoeff_real_neg {f : Vec d → ℝ}
    (k : Fin d → ℤ) :
    smoothFourierCoeff (fun x => (f x : ℂ)) (-k) =
      star (smoothFourierCoeff (fun x => (f x : ℂ)) k) := by
  unfold Torus.smoothFourierCoeff
  have hchar (x : Vec d) : Torus.torusCharacter (-k) x =
      star (Torus.torusCharacter k x) := by
    simp [Torus.torusCharacter, UnitAddTorus.mFourier_neg]
  calc
    (∫ x in Torus.unitCell d,
        Torus.torusCharacter (-k) x * (f x : ℂ)) =
      ∫ x in Torus.unitCell d,
        star (Torus.torusCharacter k x * (f x : ℂ)) := by
          apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
          intro x hx
          simp [hchar x]
    _ = star (∫ x in Torus.unitCell d,
        Torus.torusCharacter k x * (f x : ℂ)) := by
          rw [Complex.star_def]
          rw [integral_conj]

def complexEuclideanCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) (x : Vec d) : ℂ :=
  ∑ k ∈ frequencyBall M, a k * Torus.torusCharacter (-k) x

def euclideanFourierCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) (x : Vec d) : ℝ :=
  (complexEuclideanCutoff M a x).re

theorem complexEuclideanCutoff_smooth (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
    ContDiff ℝ ⊤ (complexEuclideanCutoff M a) := by
  unfold complexEuclideanCutoff
  exact ContDiff.sum (fun k hk =>
    (contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec d => a k)).mul
      (Torus.torusCharacter_contDiff (-k)))

theorem complexEuclideanCutoff_periodic (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
    IsZPeriodic (complexEuclideanCutoff M a) := by
  intro x z
  unfold complexEuclideanCutoff
  apply Finset.sum_congr rfl
  intro k hk
  have hchar := Torus.torusCharacter_periodic (-k) z x
  change a k * Torus.torusCharacter (-k) (x + Torus.intVector z) = _
  exact congrArg (fun w : ℂ => a k * w) hchar

theorem euclideanFourierCutoff_contDiff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
  ContDiff ℝ ⊤ (euclideanFourierCutoff M a) := by
  unfold euclideanFourierCutoff
  exact (Complex.reCLM.contDiff.of_le le_top).comp
    (complexEuclideanCutoff_smooth M a)

theorem euclideanFourierCutoff_periodic (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
    IsZPeriodic (euclideanFourierCutoff M a) := by
  intro x z
  unfold euclideanFourierCutoff
  exact congrArg Complex.re (complexEuclideanCutoff_periodic M a x z)

theorem periodicToTorus_euclideanFourierCutoff
    (M : ℕ) (a : (Fin d → ℤ) → ℂ) (y : UnitAddTorus (Fin d)) :
    Torus.periodicToTorus
        (fun x => (euclideanFourierCutoff M a x : ℂ)) y =
      (realFourierCutoff M a y : ℂ) := by
  have htor : complexEuclideanCutoff M a
      (Torus.unitTorusRepresentative d y) = fourierCutoff M a y := by
    simp [complexEuclideanCutoff, fourierCutoff,
      Torus.torusCharacter, Torus.toUnitTorus_unitTorusRepresentative]
  change ((complexEuclideanCutoff M a
      (Torus.unitTorusRepresentative d y)).re : ℂ) =
    ((fourierCutoff M a y).re : ℂ)
  rw [htor]

theorem mFourierCoeff_periodicToTorus_eq_smooth
    {f : Vec d → ℂ} (hper : Torus.IsZdPeriodic f)
    (hf : Continuous f) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (⟨Torus.periodicToTorus f,
        periodicToTorus_continuous_of_periodic hf hper⟩ :
          C(UnitAddTorus (Fin d), ℂ)) k = Torus.smoothFourierCoeff f k := by
  have hchar (x : UnitAddTorus (Fin d)) :
      Torus.torusCharacter k (Torus.unitTorusRepresentative d x) =
        UnitAddTorus.mFourier (-k) x := by
    simp [Torus.torusCharacter, Torus.toUnitTorus_unitTorusRepresentative]
  change (∫ x : UnitAddTorus (Fin d),
      UnitAddTorus.mFourier (-k) x • Torus.periodicToTorus f x) = _
  simp only [smul_eq_mul]
  change (∫ x : UnitAddTorus (Fin d),
      UnitAddTorus.mFourier (-k) x * Torus.periodicToTorus f x) =
    ∫ x in Torus.unitCell d, Torus.torusCharacter k x * f x
  rw [← Torus.integral_periodicToTorus_eq_unitCell
    (fun x => Torus.torusCharacter k x * f x)]
  apply integral_congr_ae
  filter_upwards with x
  change UnitAddTorus.mFourier (-k) x *
      f (Torus.unitTorusRepresentative d x) =
    Torus.torusCharacter k (Torus.unitTorusRepresentative d x) *
      f (Torus.unitTorusRepresentative d x)
  rw [← hchar x]

theorem smoothFourierCoeff_sub {f g : Vec d → ℂ}
    (hf : Continuous f) (hg : Continuous g) (k : Fin d → ℤ) :
    Torus.smoothFourierCoeff (fun x => f x - g x) k =
      Torus.smoothFourierCoeff f k - Torus.smoothFourierCoeff g k := by
  unfold Torus.smoothFourierCoeff
  rw [show (fun x => Torus.torusCharacter k x * (f x - g x)) =
      (fun x => Torus.torusCharacter k x * f x -
        Torus.torusCharacter k x * g x) by
          funext x
          ring]
  exact integral_sub
    (continuous_complex_unitCell_integrable
      ((Torus.torusCharacter_contDiff k).continuous.mul hf))
    (continuous_complex_unitCell_integrable
      ((Torus.torusCharacter_contDiff k).continuous.mul hg))

                                                          
                                                                          
                                                        
              
                    
                                                           
                                                            
                                                     
                                              
           
                                                   
                                      
                                                   
                                      
                                                 
                                                 
                                                                 
                                                                 
                              
                                                               
                                                                     
                                                                    
                                                                         
                                            
                                       
                          
                                                               
                                          
                                                   
                                                          

                                         
                                                               
                                                
                                                 
                                                   
                                      
                                               
           
                                    
                                
                                                          
                                                    
                                                           
                                                         
                                            
                                                           
                                     
                          
                                                
                                                               
                          
                                              
                                                          
                  

                                                                        
                                                    
                                                      
                                                                                     
                                          
                                                   
                                          
                                             
                               
                                    
                                                                    
                                                        
                                                                         
           
                         
                                                      
                                        
                     
                                  
                                    
                                   
                                  
                                                                
                                 
                                          
                                      
                                                     
                                                     
                                                           
                                                                         
                                            
                                           
                                       
              
                                          
                      
                                                                  
                                                         
                                                             
                                    
                                          
                                                   
                               
                        
                
                                                    
                                                                   
                                                     
                         
                      
                                                               
                                             
                                                  
                                      
                    
                                                   
                                             
                                                     
                                         
                  
                                                        
                 
                                                          
                                                           
                                        
                                                          
                                                                   
                      
                                                               
                                  
                                                         
                                  
                                                        
                                                                                
                                                 
            
                                                       
                                                                  
                            
                                                                 
                                                                        
                      
                                                                   
                                                     
                                
                                                                    
                                                       
                                                         
                                                   
            
                                                                     
                                                     
                                        
                                                     
                                              
                      
                 
          
                                            
                                                                 
                                                          
                                                       
                             
              
                                                                         
                                                     
                                       
                                                      
                                  
                               
                                       
                                                  
                         
                                 
                                         
                                              
                                                     
                                                                         
                                                                      
                                          
                                                                            
                                   
                 
                       
                                            
                                       
                                                          
        
                                                               
                                                     
                      
                                                   
                                                       
                                      
        
                                                             
                                                    
                                                                          
                                                                
                                                                     
                            
                                          
                                                               
                            
                       
                             
                     
                            
                                                 
                                              
                                                         
                                                                          
                                               
                                                   
                   
                 
                 
                                               
                                                
                                                
                                                    
                                                        
                                                        
                                                                               
                                  
                                                    
                                               
                                                        
                                                                              
                                            
                                                                         
                                                                    
                                   
        
                                               
                                
                                                    
                                          
                               
                                                                 
                                      
                                                         
                                                     
                         
                                          
                                                              
                                            

theorem smoothFourierCoeff_euclideanCutoff
    (M : ℕ) (a : (Fin d → ℤ) → ℂ)
    (ha : ∀ k, a (-k) = star (a k)) (q : Fin d → ℤ) :
    Torus.smoothFourierCoeff
        (fun x => (euclideanFourierCutoff M a x : ℂ)) q =
      if q ∈ frequencyBall M then a q else 0 := by
  let pC : Vec d → ℂ := fun x => (euclideanFourierCutoff M a x : ℂ)
  have hcont : Continuous pC := by
    exact (Complex.ofRealCLM.contDiff.comp
      (euclideanFourierCutoff_contDiff M a)).continuous
  have hper : Torus.IsZdPeriodic pC := by
    intro k x
    exact congrArg Complex.ofReal (euclideanFourierCutoff_periodic M a x k)
  let PF : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨Torus.periodicToTorus pC,
      periodicToTorus_continuous_of_periodic hcont hper⟩
  have hPF : PF = fourierCutoff M a := by
    ext y
    change Torus.periodicToTorus pC y = _
    change Torus.periodicToTorus
        (fun x => (euclideanFourierCutoff M a x : ℂ)) y = _
    rw [periodicToTorus_euclideanFourierCutoff M a y]
    exact congrFun (realFourierCutoff_complexification M a ha) y
  calc
    Torus.smoothFourierCoeff pC q = UnitAddTorus.mFourierCoeff PF q :=
      (mFourierCoeff_periodicToTorus_eq_smooth hper hcont q).symm
    _ = UnitAddTorus.mFourierCoeff (fourierCutoff M a) q := by rw [hPF]
    _ = if q ∈ frequencyBall M then a q else 0 :=
      mFourierCoeff_fourierCutoff M a q

def lowProjection (f : Vec d → ℝ) (M : ℕ) : Vec d → ℝ :=
  euclideanFourierCutoff M
    (fun k => Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k)

                                                        
                                    

theorem lowProjection_contDiff {f : Vec d → ℝ} (M : ℕ) :
    ContDiff ℝ ⊤ (lowProjection f M) :=
  euclideanFourierCutoff_contDiff M _

theorem lowProjection_periodic {f : Vec d → ℝ} (M : ℕ) :
    IsZPeriodic (lowProjection f M) :=
  euclideanFourierCutoff_periodic M _

                                              
                                   
                                          
                                                        

                                              
                                    
                                         
           
                                                              

                                         
                                                      
                                               
                                                              
             
                                 
                                                   
                                 
                                                       
                            
                                                            
                                                 
                                      
                                                             
             
                                            
                                                                      
                                                                                   
                                                                              
             
                                                                
                                                                       
                                                                       
                                                                               
             
                                                                     
                                  
                              
                                                
                                                    
                                                
                                              
                                   
                              
                                                
                                              
                                                       
                                                              
              
                          
                                       
                               
                                               
                                       
                               
                                     
                                                           
                         
                                        
                                          
                         
                                                    
                               
                                                                        
                                                     
                                        
                                            
                            
                                          
                                    
                                     
                  
                                        
                                          
               
                
                                                     
                               
                                                                        
                                                     
                                        
                                            
                              
                                          
                                     
                               
               
                
                  
             
                                                            
                                                  
                                                            
                                                     

                                          
                                   
                                                          
                   
                                                          
                                          
                                                          
                                                                   
                                                                  
                               
                                                                             
                                                               
                                                  
                                                
                                              
                              
                                           
                                                 
               
                                     
                      
                      
                                                                 
                                                                 
                                                                         
                                            
                                                   
                                                              
                                                                
              
                                        
                                                   
                                            
                                                                
              
                                        
                          
                                                              

                                              
                                          
       
                                                      

                                                   
                                                   
                                               
                                                          
                                                                       
                                           
                                   
                                                             
                                

                                    
                                                                                
                                                                                
                                                                        
                                
                                                                    
                                                                   
                                      
                                                 
                                                                           
                                                     
                                                               
                              
                                                                  
                                                               
                                                                     
                                                                 
                                                       
                                          
                                 
                                                     
                                                                  
                                                  
                                                    
                                                                
                            

                                                                    
                                                                          
                                                      
                                
                                                             
                                                               
                        
                                      
                                
                                                     
                                               
                            
                                                               
           
                                      
                                      
                                                                          
                                                         
                
                                              
                                              
                                                           
                                                 
                
                                                                                      
                  
             
                                                            
                      
                                         
                                                                       
               
         
                
                                                                
                                                 
                                                
                                                            
             
                                                      
                
                                           
                                                         
                                        
                                   
                                                                      
        
                                            
                                                          
                                               
                                                                 
            
                               
                  
                                            
                                                                                
                                  
                                                                           
                                                                        
                      
                                      
                      
                                                         
                
                                  
                      
                                                          
                                                                          
                        
                                            
              
                                            
                                                          
                               
                  
                                              
                                                                    
                  
                            
                                              
                                              
                                                                       
                                             
                
                                                     
                
                                  
                                                                     
                                                  
        
                                     
                                                                
                                   
                                 
                                                           
                                              
                      
                 
                                                           
                                           
                                                      
                                                                       
                      
                                                         
                                                             
                                                       
                           
                                                              
        
                                                             
                                      
                                                                           
                          
                               
                                                                  
                                                
                                                              
                                  
                               
                                                                
                        
                                                              
                                                 
                                                                   
                                     
                
                                       
                                                                         
                                                    
                              
                                          

                                                              
                                                      
                                                                    

                                                              
                                                         
                                                           
                                                                          
                                                        
                                                                         
                                                  
                                                                   
                                   
                                                                                       
                                                                            
                                                                              
                                                                            
                                                                              
                                                                                 
                                         
                            

                                                            
                     
                                                         
                                                           
                                                   
                                                                   
               
         
                                               
                                               
                                                                        
                                                  
                                                      
              
          
             
                                              
                                                 
                                                 
      
                                              
                                     
                                               
                                                     
                                                           
                                                                  
                                                              
                                                     

                                                                                
                                                  
                                                                                
                                          
                                                                      
                                                                             
                                                     
                             
                                                              
                                                         
                               
                                                           
                                                
                                                              
                                               
                                               
                                                       
                                
                                    
                                                                             
                                                                             
                       
             
                                                
                                                     
             
                                              
                                                         
             
                                             
                                                                
              
                 
                                                     
             
                                              
                                                              
                                             
             
                                                                
              
        
                                                                          
                                                   
                            
                                                                 
                                             
                                      
                                                   
                         
                                                                 
                                
            
                 
                                                                            
                                                                    
                                  
                                         
                                    
                                  
                             
                                           
                                            
                              
               
                
                                                  
                                                  
                                    
               
            
                 
                                                
                                                 
                                 
                                                    
            
                                                   
                                                                               
                     
                                                 
                
                        
                                                
                                                     
                 
            
                                    
                                                                
                                     
                                                      
                                                   
                                                                       
                                   
                            
                   
                                                                 
                      
                                     
                              
               
              
                                                 
                                       
                                                         
                                                           
                                                                            
                                                     
                             
                                                 
                                                  
            
                                                        
                                                    
                                                                      
                                    
                          
                                                                            
                                                    
                                               
                                                           
                                                                    
          
                              
                                                       
                                      
                                              
                     
                                            
                                                           
             
                
        
                                          
                                               
                                                             

end

end AVenhance.Infra.Ergodic
