module

public import RequestProject.External
public import RequestProject.TorusFourier

/-!
# Section 2.1: an elementary stretching estimate

The shears `H`, `V`, the commutator `F = V⁻¹ ∘ H⁻¹ ∘ V ∘ H`, its rotated and translated copies
`G_{ι,z}`, the random matrix law `Q`, and the negative moment estimate (Lemma 2.5).

Maps of the torus isotopic to the identity are represented by their lifts `Φ : ℝ² → ℝ²`
satisfying `Φ (x + n) = Φ x + n` for `n ∈ ℤ²`.  The uniform distribution on `𝕋²` is Lebesgue
measure on the unit cell, and the uniform distribution on `{0,1}` is the uniform distribution on
`Bool`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Matrix

noncomputable section

namespace AnomDiss

/-- The horizontal shear `H(x,y) = (x + (2π)⁻¹ sin(2πy), y)`. -/
def shearH (p : Pt 2) : Pt 2 := ![p 0 + (2 * π)⁻¹ * Real.sin (2 * π * p 1), p 1]

/-- The vertical shear `V(x,y) = (x, y + (2π)⁻¹ sin(2πx))`. -/
def shearV (p : Pt 2) : Pt 2 := ![p 0, p 1 + (2 * π)⁻¹ * Real.sin (2 * π * p 0)]

/-- `H⁻¹`. -/
def shearHinv (p : Pt 2) : Pt 2 := ![p 0 - (2 * π)⁻¹ * Real.sin (2 * π * p 1), p 1]

/-- `V⁻¹`. -/
def shearVinv (p : Pt 2) : Pt 2 := ![p 0, p 1 - (2 * π)⁻¹ * Real.sin (2 * π * p 0)]

/-- `F = V⁻¹ ∘ H⁻¹ ∘ V ∘ H`. -/
def mapF : Pt 2 → Pt 2 := shearVinv ∘ shearHinv ∘ shearV ∘ shearH

/-- `F⁻¹ = H⁻¹ ∘ V⁻¹ ∘ H ∘ V`. -/
def mapFinv : Pt 2 → Pt 2 := shearHinv ∘ shearVinv ∘ shearH ∘ shearV

/-- The quarter turn `𝒥(x,y) = (-y,x)`. -/
def rotJ (p : Pt 2) : Pt 2 := ![-p 1, p 0]

/-- `𝒥⁻¹(x,y) = (y,-x)`. -/
def rotJinv (p : Pt 2) : Pt 2 := ![p 1, -p 0]

/-- `𝒥^ι Φ 𝒥^{-ι}` for `ι ∈ {0,1}` (`false = 0`, `true = 1`). -/
def conjJ (ι : Bool) (Φ : Pt 2 → Pt 2) : Pt 2 → Pt 2 :=
  if ι then rotJ ∘ Φ ∘ rotJinv else Φ

/-- `G_{ι,z} = τ_z ∘ 𝒥^ι F 𝒥^{-ι} ∘ τ_{-z}`. -/
def mapG (ι : Bool) (z : Pt 2) (x : Pt 2) : Pt 2 := z + conjJ ι mapF (x - z)

                                                   
                                                                                  

                                   
def jac (Φ : Pt 2 → Pt 2) (x : Pt 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => fderiv ℝ Φ x (Pi.single j 1) i

/-- A map `ℝ² → ℝ²` is a lift of a torus map isotopic to the identity
(`Φ (x + n) = Φ x + n` for every `n ∈ ℤ²`, i.e. `Φ - id` is periodic). -/
def IsLift (Φ : Pt 2 → Pt 2) : Prop := ∀ x (n : Fin 2 → ℤ), Φ (x + intVec n) = Φ x + intVec n

                      
                                                       

                        
                                                      


                                                              
noncomputable def matCLM (A : Matrix (Fin 2) (Fin 2) ℝ) : Pt 2 →L[ℝ] Pt 2 :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

lemma matCLM_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Pt 2) : matCLM A v = A *ᵥ v := rfl

lemma matCLM_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) : (matCLM A).comp (matCLM B) = matCLM (A * B) := by
  apply ContinuousLinearMap.ext
  intro v
  change A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v
  exact Matrix.mulVec_mulVec v A B

lemma jac_eq_of_hasFDerivAt {Φ : Pt 2 → Pt 2} {x : Pt 2} {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : HasFDerivAt Φ (matCLM A) x) : jac Φ x = A := by
  ext i j
  simp [jac, h.fderiv, matCLM_apply, Matrix.mulVec_single]

lemma hasFDerivAt_shearX (f : ℝ → ℝ) (f' : ℝ) (p : Pt 2) (hf : HasDerivAt f f' (p 1)) :
    HasFDerivAt (fun p : Pt 2 => ![p 0 + f (p 1), p 1]) (matCLM !![1, f'; 0, 1]) p := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · change HasFDerivAt (fun q : Pt 2 => q 0 + f (q 1))
      ((ContinuousLinearMap.proj (0 : Fin 2)).comp (matCLM !![1, f'; 0, 1])) p
    have h := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p).fun_add
      (hf.comp_hasFDerivAt p (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p))
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp [matCLM_apply, dotProduct, Fin.sum_univ_two]
  · change HasFDerivAt (fun q : Pt 2 => q 1)
      ((ContinuousLinearMap.proj (1 : Fin 2)).comp (matCLM !![1, f'; 0, 1])) p
    convert hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [matCLM_apply, dotProduct, Fin.sum_univ_two]

lemma hasFDerivAt_shearY (g : ℝ → ℝ) (g' : ℝ) (p : Pt 2) (hg : HasDerivAt g g' (p 0)) :
    HasFDerivAt (fun p : Pt 2 => ![p 0, p 1 + g (p 0)]) (matCLM !![1, 0; g', 1]) p := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · change HasFDerivAt (fun q : Pt 2 => q 0)
      ((ContinuousLinearMap.proj (0 : Fin 2)).comp (matCLM !![1, 0; g', 1])) p
    convert hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [matCLM_apply, dotProduct, Fin.sum_univ_two]
  · change HasFDerivAt (fun q : Pt 2 => q 1 + g (q 0))
      ((ContinuousLinearMap.proj (1 : Fin 2)).comp (matCLM !![1, 0; g', 1])) p
    have h := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p).fun_add
      (hg.comp_hasFDerivAt p (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p))
    convert h using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp [matCLM_apply, dotProduct, Fin.sum_univ_two]
      ring


lemma hasDerivAt_sinShear (y : ℝ) :
    HasDerivAt (fun y => (2 * π)⁻¹ * Real.sin (2 * π * y)) (Real.cos (2 * π * y)) y := by
  have h := ((Real.hasDerivAt_sin (2 * π * y)).comp y
    ((hasDerivAt_id y).const_mul (2 * π))).const_mul (2 * π)⁻¹
  convert h using 1
  · rfl
  · field_simp [Real.pi_ne_zero]

lemma hasDerivAt_negSinShear (y : ℝ) :
    HasDerivAt (fun y => -((2 * π)⁻¹ * Real.sin (2 * π * y))) (-Real.cos (2 * π * y)) y :=
  (hasDerivAt_sinShear y).neg

lemma hasFDerivAt_shearH (p : Pt 2) :
    HasFDerivAt shearH (matCLM !![1, Real.cos (2 * π * p 1); 0, 1]) p :=
  hasFDerivAt_shearX _ _ p (hasDerivAt_sinShear (p 1))

lemma hasFDerivAt_shearV (p : Pt 2) :
    HasFDerivAt shearV (matCLM !![1, 0; Real.cos (2 * π * p 0), 1]) p :=
  hasFDerivAt_shearY _ _ p (hasDerivAt_sinShear (p 0))

lemma hasFDerivAt_shearHinv (p : Pt 2) :
    HasFDerivAt shearHinv (matCLM !![1, -Real.cos (2 * π * p 1); 0, 1]) p := by
  have e : shearHinv = fun p : Pt 2 => ![p 0 + -((2 * π)⁻¹ * Real.sin (2 * π * p 1)), p 1] := by
    funext q; simp [shearHinv, sub_eq_add_neg]
  rw [e]; exact hasFDerivAt_shearX _ _ p (hasDerivAt_negSinShear (p 1))

lemma hasFDerivAt_shearVinv (p : Pt 2) :
    HasFDerivAt shearVinv (matCLM !![1, 0; -Real.cos (2 * π * p 0), 1]) p := by
  have e : shearVinv = fun p : Pt 2 => ![p 0, p 1 + -((2 * π)⁻¹ * Real.sin (2 * π * p 0))] := by
    funext q; simp [shearVinv, sub_eq_add_neg]
  rw [e]; exact hasFDerivAt_shearY _ _ p (hasDerivAt_negSinShear (p 0))

                                   
                    
                                                                                 
                                                               
                                                     
                                                       
                                                                              
                                                           
                             
         

lemma contDiff_vec2 {f g : Pt 2 → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p => ![f p, g p]) := by
  rw [contDiff_pi]
  intro i; fin_cases i
  · simpa using hf
  · simpa using hg

lemma contDiff_shearH : ContDiff ℝ ∞ shearH :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_shearV : ContDiff ℝ ∞ shearV :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_shearHinv : ContDiff ℝ ∞ shearHinv :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

lemma contDiff_shearVinv : ContDiff ℝ ∞ shearVinv :=
  contDiff_vec2 (by fun_prop) (by fun_prop)

                                                                                    

                                                                                          

                                          
                                                                                          

lemma contDiff_mapFinv : ContDiff ℝ ∞ mapFinv :=
  contDiff_shearHinv.comp (contDiff_shearVinv.comp (contDiff_shearH.comp contDiff_shearV))

                                                                         
                                  
         
            
                                                       

                                                                      
                                                                                             

                                                                            
                                                                                                

               

lemma vec2_ext {p q : Pt 2} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  funext i; fin_cases i <;> assumption

                                                               
                                                                      

                                                               
                                                                      

                                                               
                                                                      

                                                               
                                                                      

                                                       
                                                              

                                                       
                                                              

                                                          
                                                                                              

                                                          
                                                                                              

                                                                                  
                                     
         
             
                                               

                                                                               
                                                

                                                                               
                                                


            

lemma sin_two_pi_add_int (y : ℝ) (n : ℤ) : Real.sin (2 * π * (y + n)) = Real.sin (2 * π * y) := by
  rw [show 2 * π * (y + n) = 2 * π * y + n * (2 * π) by ring, Real.sin_add_int_mul_two_pi]

lemma isLift_shearH : IsLift shearH := fun x n =>
  vec2_ext (by simp [shearH, intVec, sin_two_pi_add_int]; ring) (by simp [shearH, intVec])

lemma isLift_shearV : IsLift shearV := fun x n =>
  vec2_ext (by simp [shearV, intVec]) (by simp [shearV, intVec, sin_two_pi_add_int]; ring)

lemma isLift_shearHinv : IsLift shearHinv := fun x n =>
  vec2_ext (by simp [shearHinv, intVec, sin_two_pi_add_int]; ring) (by simp [shearHinv, intVec])

lemma isLift_shearVinv : IsLift shearVinv := fun x n =>
  vec2_ext (by simp [shearVinv, intVec]) (by simp [shearVinv, intVec, sin_two_pi_add_int]; ring)

lemma IsLift.comp {Φ Ψ : Pt 2 → Pt 2} (hΦ : IsLift Φ) (hΨ : IsLift Ψ) : IsLift (Φ ∘ Ψ) :=
  fun x n => by simp only [Function.comp, hΨ x n, hΦ _ n]

                                  
                                                                                  

lemma isLift_mapFinv : IsLift mapFinv :=
  isLift_shearHinv.comp (isLift_shearVinv.comp (isLift_shearH.comp isLift_shearV))

                                                     
                                                               
                                                                        

                                                  
                                                         
                                                                  

                                                                                          
         
            
             
                                                                                        
           
                                  

                                                                            
                                                                                                      
      


                            

                                                             
                                                                                         
                                                                  

                                                                   
                                                                                            
                                                                     

                                                                                          
                                                           
                                                                                  
                                                
         
                          
                                                                        
                                                                       
                                                                    
                                                            
                                                                               
                                                         
                                                      
                                 
             

                                                                                         
                                            
                                                           
                                                                    
                

                                                          
                                                                                                 
                              

                                                                             
                                                                                 
                                                      
                                                              
                                     
                                                             
                                                          

                                                                                              
        
                                
                                                                    
                                       
                                                                                     
                                                                                      
                                                                              
                                                            
                                                         
                                                                              
                                                                                  
                                              
                                                                           
                                                                                          
                                                                     
                                                             
                                                                     
                                                                                   
                                                                                   

                                                        
                                                                            
                           
                                                             
                                                                 
                                           
                                       
                                                                       
                                                         
                                                         
                                                                
                                                                
                                                                 
                                                                      
                                                                        
                                                                             
                                                                                  
                         
                                
                                
                                                                   
                                                                                                 
                                                                   
                                            
                                                              

                                          

                                                     
def uniformBool : Measure Bool := Measure.uniformOfFinset Finset.univ

                                                                                    
                                                                                   
                                                             

                                                                               
def uniformTorus : Measure (Pt 2) := volume.restrict (cell 2)

/-- Law of one pair `(ι, z)`: independent uniform variables on `{0,1}` and `𝕋²`. -/
def stepMeasure : Measure (Bool × Pt 2) := uniformBool.prod uniformTorus

instance : IsProbabilityMeasure uniformTorus :=
  ⟨by simp [uniformTorus, cell, Real.volume_Icc_pi]⟩

instance : IsProbabilityMeasure uniformBool := by
  constructor
  norm_num [uniformBool, Measure.uniformOfFinset, Fintype.sum_bool]
  simpa only [one_div] using ENNReal.add_halves 1

instance : IsProbabilityMeasure stepMeasure := by unfold stepMeasure; infer_instance

/-- The matrix `𝒥` acting on `ℝ²`. -/
def matJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The matrix `𝒥⁻¹`. -/
def matJinv : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- `A(Z) = DF⁻¹(Z)ᵀ`. -/
def matA (Z : Pt 2) : Matrix (Fin 2) (Fin 2) ℝ := (jac mapFinv Z)ᵀ

/-- `Q = 𝒥^ι A 𝒥^{-ι}` (Definition 2.3). -/
def matQ (w : Bool × Pt 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  if w.1 then matJ * matA w.2 * matJinv else matA w.2

/-- The entries of a `2 × 2` matrix, as a point of `Fin 2 → Fin 2 → ℝ` (used to speak about
laws of random matrices). -/
def matEntries (A : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => A i j


                                                         
                                         
         
                                                                           
                                                       
                                                      
                     
                           

                                                                                               
                             
                                                                 

                                                                                          
                                                                                     
                                                               
                                   
                                 

                                                              
                                                                             
                
                                                                
                                                        
                                                                                 
                                                     
                                                                       
                             
                                                                                
                                                                          
                                  

lemma jac_mapFinv_periodic (y : Pt 2) (n : Fin 2 → ℤ) :
    jac mapFinv (y + intVec n) = jac mapFinv y := by
  have : fderiv ℝ mapFinv (y + intVec n) = fderiv ℝ mapFinv y := by
    rw [← fderiv_comp_add_right]
    have e : (fun x => mapFinv (x + intVec n)) = fun x => mapFinv x + intVec n := by
      funext x; exact isLift_mapFinv x n
    rw [e, fderiv_add_const]
  simp [jac, this]

lemma continuous_jac_mapFinv : Continuous (jac mapFinv) := by
  have hc : Continuous (fderiv ℝ mapFinv) := contDiff_mapFinv.continuous_fderiv (by simp)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [jac, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((ContinuousLinearMap.apply ℝ (Pt 2) (Pi.single j 1 : Pt 2)).continuous.comp hc)

lemma continuous_matQ (ι : Bool) : Continuous fun Z => matEntries (matQ (ι, Z)) := by
  have hA : Continuous matA := by
    unfold matA
    exact continuous_jac_mapFinv.matrix_transpose
  have hentries : Continuous (matEntries : Matrix (Fin 2) (Fin 2) ℝ → Fin 2 → Fin 2 → ℝ) :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  cases ι
  · simpa only [matQ, Bool.false_eq_true, if_false, Function.comp_def] using hentries.comp hA
  · simpa only [matQ, if_true, Function.comp_def] using
      hentries.comp ((continuous_const.matrix_mul hA).matrix_mul continuous_const)

                                                                                   
           
                                         

                                                     
                                                                                 
         
                                        
                         
                                                         
                                                                        
                                                  
                                                                           
                                                  
                                 

                                                                                   
                                                                                     
                                                                                            
                                               
                                                                    
                                                                    
          
                                                                      
                                                             
                                    
                                                   
                                                                              
            

                                                                          
                                          
                                                                                    
                                                          
                                                                         
                                                                   
                                                         
                                                                               
                                                                  
                                                                                          
                 
                     
           
                                                                                          
                                                        
                                                                       
                     
           
                                                                               
                                                                            


                                                                               
def prodQ {L : ℕ} (w : Fin L → Bool × Pt 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (List.ofFn fun i => matQ (w i)).reverse.prod

/-- The negative moment bound `sup_{|e|=1} 𝔼|Q_L ⋯ Q_1 e|^{-σ} ≤ 1/(128 q^σ)`. -/
def NegMomentBound (q σ : ℝ) (L : ℕ) : Prop :=
  ∀ e : Pt 2, euclNorm e = 1 →
    ∫ w, euclNorm ((prodQ w) *ᵥ e) ^ (-σ) ∂(Measure.pi fun _ : Fin L => stepMeasure)
      ≤ 1 / (128 * q ^ σ)


/-! ### The random block map (Definition 2.6) -/

/-- The block map `𝓕 = G_{ι_L,z_L} ∘ ⋯ ∘ G_{ι_1,z_1}`. -/
def blockMap {L : ℕ} (w : Fin L → Bool × Pt 2) (x : Pt 2) : Pt 2 :=
  (List.ofFn w).foldl (fun y p => mapG p.1 p.2 y) x

                                                                       
                                                                      
                                                      

                                          

                                                                    
                                                                                            
                                 
              
                                                                                 

                                                                    
                                                                                            
                                 
              
                                                                                 

                                                          
                                                       
                                                           
                                                                                


lemma periodic_bdd {d : ℕ} {F : Type*} [NormedAddCommGroup F] (h : Pt d → F) (hc : Continuous h)
    (hp : IsPeriodic h) : ∃ C, ∀ y, ‖h y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Pt d)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun y => ?_⟩
  set n : Fin d → ℤ := fun i => ⌊y i⌋
  have hz : y - intVec n ∈ Icc (0 : Pt d) 1 := by
    constructor <;> intro i <;> simp only [Pi.sub_apply, intVec, Pi.zero_apply, Pi.one_apply, n]
    · exact sub_nonneg.2 (Int.floor_le _)
    · linarith [Int.lt_floor_add_one (y i)]
  have := hp (y - intVec n) n
  rw [sub_add_cancel] at this
  rw [this]; exact hC _ hz

lemma iteratedFDeriv_add_const_of_ne {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) {n : ℕ}
    (hn : n ≠ 0) (c : F) (x : E) :
    iteratedFDeriv ℝ n (fun y => f y + c) x = iteratedFDeriv ℝ n f x := by
  have : (fun y => f y + c) = f + fun _ => c := rfl
  rw [this, iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    contDiffAt_const, iteratedFDeriv_const_of_ne hn, Pi.zero_apply, add_zero]

/-- A family of smooth self-maps of `ℝ²` all of whose positive-order derivatives are bounded
uniformly over the family (for each finite range of orders). -/
def UnifDerivBdd (S : Set (Pt 2 → Pt 2)) : Prop :=
  (∀ Φ ∈ S, ContDiff ℝ ∞ Φ) ∧
    ∀ n : ℕ, ∃ C, ∀ Φ ∈ S, ∀ x, ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Φ x‖ ≤ C

lemma UnifDerivBdd.comp {S T : Set (Pt 2 → Pt 2)} (hS : UnifDerivBdd S) (hT : UnifDerivBdd T) :
    UnifDerivBdd {Φ | ∃ g ∈ S, ∃ f ∈ T, Φ = g ∘ f} := by
  refine ⟨?_, fun n => ?_⟩
  · rintro _ ⟨g, hg, f, hf, rfl⟩; exact (hS.1 g hg).comp (hT.1 f hf)
  obtain ⟨Cg, hCg⟩ := hS.2 n
  obtain ⟨Cf, hCf⟩ := hT.2 n
  set D := max 1 Cf
  set C := max 0 Cg
  refine ⟨n.factorial * C * D ^ n, ?_⟩
  rintro _ ⟨g, hg, f, hf, rfl⟩ x i hi1 hin
  have hgs := hS.1 g hg
  have hfs := hT.1 f hf
  set g' : Pt 2 → Pt 2 := fun y => g y + (-g (f x))
  have hg's : ContDiff ℝ ∞ g' := hgs.add contDiff_const
  have hcomp : iteratedFDeriv ℝ i (g ∘ f) x = iteratedFDeriv ℝ i (g' ∘ f) x := by
    have : g' ∘ f = fun y => (g ∘ f) y + (-g (f x)) := rfl
    rw [this, iteratedFDeriv_add_const_of_ne (hgs.comp hfs) (by omega)]
  have key := norm_iteratedFDeriv_comp_le (n := i) (N := ∞) (C := C) (D := D) hg's hfs
    (by exact_mod_cast le_top) x ?_ ?_
  · rw [hcomp]
    refine key.trans ?_
    have hD : 1 ≤ D := le_max_left _ _
    have hC : 0 ≤ C := le_max_left _ _
    gcongr
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDeriv_zero]
      simp only [g', add_neg_cancel, norm_zero]
      exact le_max_left _ _
    · rw [iteratedFDeriv_add_const_of_ne hgs (by omega)]
      exact (hCg g hg (f x) j hj0 (hj.trans hin)).trans (le_max_right _ _)
  · intro j hj1 hj
    calc _ ≤ Cf := hCf f hf x j hj1 (hj.trans hin)
      _ ≤ D := le_max_right _ _
      _ ≤ D ^ j := le_self_pow₀ (le_max_left _ _) (by omega)

                                                                                          
                                                                       
                                                                                    
           
                                      
                                                                                        
                                                 


lemma UnifDerivBdd.mono {S T : Set (Pt 2 → Pt 2)} (hT : UnifDerivBdd T) (h : S ⊆ T) :
    UnifDerivBdd S :=
  ⟨fun Φ hΦ => hT.1 Φ (h hΦ), fun n => (hT.2 n).imp fun _ hC Φ hΦ => hC Φ (h hΦ)⟩

                                                                                          
                                                                  
                  
                                                
                
                        
                                                                                  
                                          
                                            
                                                          
                                        
                                            

                                                                                                
                  
                                                                                      
                                                                                          
                                                                                         
                                                                          

                                                                                     
                              
                                                                
                          
                        
                                                                           
                                                               
                                                             
                        
                                  
                                                          
         
                                                  
                                                   

                                                                                   
                                                                                                 
                                                   
                                               

                                                                                         
                                                          
                                                
                                                      
                                               

                                                               
                                                                 
                                                                               
                                             

                                  
                                                              
                                                               
                  
           
                                  
                         
                                          
                
                                              
                         
                                                                  
                                                            

                                  
                                                              
                                                                  
                  
           
                                  
                         
                                          
                
                                                 
                         
                                                                  
                                                            

                                                          
                                                                                 
                                                      
                                               
                                               
                                         
                                                                                    
                       
                                                                                       
                        


lemma continuous_matQ_joint : Continuous matQ := by
  rw [continuous_prod_of_discrete_left]
  intro ι
  exact continuous_matQ ι

lemma continuous_prodQ (L : ℕ) : Continuous fun w : Fin L → Bool × Pt 2 => prodQ w := by
  unfold prodQ
  simp only [List.ofFn_eq_map, ← List.map_reverse]
  exact continuous_list_prod _ fun i _ => continuous_matQ_joint.comp (continuous_apply i)

                                        
                                                                     
                                                                           
                                  


                                                                    
                                                          
                                                   
                                                
                                                                                     
                                                                                    
                                      
                                                                              
                               
                                                  
                                                                                
                              
                                    
                   
                                   
                                                          
            
                                       
                                                                                                  
                                                      
                                                    
                                                           
                                                                  
                   
              


                                                                                            
                                                               
                                                                      
                                                                          
                                                    
                                                           
                                                                 

                                
                                                                         
                                                                   
                  
                                                          
            

                                    
                                                                                  
                                                                            
                                                                                          
                                                                      
        
                                       
                                                                                                 
               
                                      
         
                                                      
                       
                                                            
            

                                                                           
                                                                                                      
                                                                                          
     

                                                          
                                                              
                                                                                
                 

                                                                           
                              

                                                                                              
                                                                 

                                                                                
                                                                               
                             
                                                
                                                                  
         

                                             
                             
                                           
                                

                                                                               
                                                          
                                                           
                                                                 
                                                     
                                                                                           
                                                                        
                                                        

                                          
                                                                                      
                  
           
                                                                                                 
                                              
                                     
                
                                    
                                                                                             
                                              
                                                                                         
                                                                     
                                                                          
                                                                              
                                                   


                                                                                              
                                                                                     
                                           
                                                                

                                                                                
                                                                               
                                                             
                                                                      
                                             
          
                                                                                   
                               
                                    
                                                  
                                                                                     
                                                                                           
            

                                                                                
                                                                               
                                                             
                                                                      
                                             
          
                                                                                        
                                    
                                    
                                                  
                                                                                      
                                                                                            
            

                                                         
                                                                         
                                                                                                   
                                                                              
                                                                                                
                                                                      
         
          
                                       

                                                                                        
                                              
                                                 
                                                        
                                                                                         
                                 
           
                     
                                                
                
                                                                                         
                                                            
                              
                                                                                                  
                                                                                                    
                                            
                                                                         
                                                                    
                                                                         
                                                
                                                                         
                                             
                                                                   
                                           
                                                                                      
                                                                   
                                                             
                                                   
                                                                   
                                                                                       
                                                                                          
                                                      
                                                                                
                                                                           
                                                      
                                          
                                                     
                                                                   
                                                        
                                                                                                
                                                                                                
                                                                                      
                                                          
                                                    
                                           
                                                                             
                                                                                                  
                                                                               
                                                                                                      
                                                                                                    
                                                                   
                                                                                                 
                           
                                                                                                
                                                           
                                                                 
                                                                           
                                                                              
                                                                     
                                                                 

                                                                                               
                                                       
                                                                                            
                                                                                  
                                                                         
                                                       
                                                        
                                                                                      
                                      
                                                          
                                                                           
                                                                                   
                                                           
                                                                                                   
                                                    
                                                                   
                                        
                                          
                                                                               
                                   
                                              

end AnomDiss
