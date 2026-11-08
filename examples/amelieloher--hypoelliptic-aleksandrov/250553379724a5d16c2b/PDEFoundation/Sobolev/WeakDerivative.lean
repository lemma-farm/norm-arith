module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weak first derivatives on native vector domains

The raw integration-by-parts predicates remain compatible with LIH. A bundled
test-function facade packages smoothness, compact support, and support
containment for later PDE proofs.
-/

@[expose] public section

namespace PDE

/-- A smooth compactly supported test function whose topological support lies
inside `U`. -/
structure WeakTestFunction {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (WeakTestFunction U) (fun _ => Vec d → ℝ) where
  coe φ := φ.toFun

/-- The classical `i`th derivative of a bundled test function. -/
noncomputable def WeakTestFunction.partialDeriv
    {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (x : Vec d) : ℝ :=
  (fderiv ℝ φ.toFun x) (basisVec i)

/-- `gi` is the `i`th weak derivative of `u` on `U`. -/
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

/-- `Du` is a coordinate weak gradient of `u` on `U`. -/
def HasWeakGradientOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

theorem hasWeakPartialDerivOn_iff_forall_testFunction
    {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} :
    HasWeakPartialDerivOn U i u gi ↔
      ∀ φ : WeakTestFunction U,
        ∫ x in U, u x * φ.partialDeriv i x ∂MeasureTheory.volume =
          -∫ x in U, gi x * φ x ∂MeasureTheory.volume := by
  constructor
  · intro h φ
    exact h φ.toFun φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  · intro h φ hφSmooth hφCompact hφSupport
    exact h
      { toFun := φ
        contDiff := hφSmooth
        hasCompactSupport := hφCompact
        tsupport_subset := hφSupport }

namespace HasWeakPartialDerivOn

                                                                              
            
                                                       
                                     
                                                                          
                                                                          
                                          
                                            
                              
                  
                                                               
                                                          
                                                        
                                    
                                                     
               
                                                                          
                                                                  
               
                                                                          
                                                                  
                
                                                                     
                                    
                               
                                                                      
                
                                                                     
                                    
                               
                                                                      
                   
                                                  
                
                                                  
                   
                                                  
                
                                                  
                 
                                                                         
                                                        
                                                               
                 
                                                                         
                                                        
                                                               
                 
                                                    
                                                          
                                                 
                                                 
                         
                         
                   
                                                                     
          
                                                             
                                               
                                         
                                                                          
                          
                    
                                                        
                                                              
                                                             
                                         
                   
                                                  
                
                                                                
                                                     
        
                                                      
                                                              
                              
                                                                   
                                                                             
                       
                       
                                                                           
                                          
                               

end HasWeakPartialDerivOn

theorem HasWeakPartialDerivOn.restrict {d : ℕ}
    {U V : Set (Vec d)} (_hVOpen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := by
  intro φ hφSmooth hφCompact hφSupport
  have hφSupportU : tsupport φ ⊆ U := hφSupport.trans hVU
  have hWeak := h φ hφSmooth hφCompact hφSupportU
  have hValueZero :
      ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSupport hx')
    have hφEq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hxNotIn |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp
  have hGradZero :
      ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport
      (fun hx' => hx (hφSupport hx'))]
  have hValueZeroU :
      ∀ x, x ∉ U → u x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    fun x hx => hValueZero x (fun hx' => hx (hVU hx'))
  have hGradZeroU :
      ∀ x, x ∉ U → gi x * φ x = 0 :=
    fun x hx => hGradZero x (fun hx' => hx (hVU hx'))
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hValueZero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hGradZero,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hValueZeroU,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hGradZeroU,
    hWeak]

theorem HasWeakGradientOn.restrict {d : ℕ}
    {U V : Set (Vec d)} (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i
  exact (h i).restrict hVOpen hVU

theorem HasWeakPartialDerivOn.of_contDiff {d : ℕ}
    {U : Set (Vec d)} {i : Fin d} {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDerivOn U i f
      (fun x => (fderiv ℝ f x) (basisVec i)) := by
  intro φ hφSmooth hφSupport hφSubset
  let ei : Vec d := basisVec i
  have hfDiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hφDiff : Differentiable ℝ φ :=
    hφSmooth.differentiable (by simp)
  have hfCont : Continuous f := hfDiff.continuous
  have hφCont : Continuous φ := hφDiff.continuous
  have hfderivφCont :
      Continuous (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using
      (hφSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderivfCont :
      Continuous (fun x => (fderiv ℝ f x) ei) := by
    simpa [ei] using
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφFderivSupport :
      HasCompactSupport (fun x => (fderiv ℝ φ x) ei) := by
    simpa [ei] using hφSupport.fderiv_apply (𝕜 := ℝ) ei
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simpa [ei] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        ((hfderivfCont.mul hφCont).integrable_of_hasCompactSupport
          hφSupport.mul_left)
        ((hfCont.mul hfderivφCont).integrable_of_hasCompactSupport
          hφFderivSupport.mul_left)
        ((hfCont.mul hφCont).integrable_of_hasCompactSupport
          hφSupport.mul_left)
        (fun x _ => hfDiff x) (fun x _ => hφDiff x)
  · intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSubset hx')
    simp [image_eq_zero_of_notMem_tsupport hxNotIn]
  · intro x hx
    have hxNotIn : x ∉ tsupport φ := fun hx' => hx (hφSubset hx')
    have hφEq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hxNotIn |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp

theorem HasWeakGradientOn.of_contDiff {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakGradientOn U f
      (fun x i => (fderiv ℝ f x) (basisVec i)) := by
  intro i
  exact HasWeakPartialDerivOn.of_contDiff hf

end PDE
