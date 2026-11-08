module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Util/Chart/FlatChartDerivs.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.TangentBundle.LocallyConstant

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false


/-!
# Tangent bundle — chart-derivative engineering

Flat-codomain (type-erased) chart-derivative wrappers and the framework's
parametric chart-mfderiv smoothness theorems.

The flat-typed wrappers retype the dependent codomain
`E →L[ℝ] TangentSpace I y` to `E →L[ℝ] E` via the def-eq
`TangentSpace I y = E`, hiding the cast. Smoothness statements on
`M → (E →L[ℝ] E)` are the user-facing API; clients never see the
def-eq bridge.

Most helpers are `private` (Layer 1-4 framework infrastructure for
constant-section smoothness, finite-dim continuous linear map lift, and chart-inverse
smoothness via `inverse` composition). The four public theorems are
`continuousLinearMapAtFlat_contMDiffAt`, `symmLFlat_mdifferentiableAt`,
`contMDiff_constSection_TangentSpace` (used by `SmoothVectorField.const`).
-/

open scoped ContDiff Manifold Topology

namespace TangentBundle
                                                                                 
                                             
                           
                                                        
                                                                 
                                                                          
                            
                                                   
                                                 
                                                                  
noncomputable def continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
                                                                                 
                                                                   
                                                        
                                                                 
                                                                          
                                   
                                                                

                                                                       

                                                                                                  
                                                                  
                                                                    
                                                
theorem continuousLinearMapAtFlat_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (b₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) b₀) b₀ := by
  refine (contMDiffAt_const (c := ContinuousLinearMap.id ℝ E)).congr_of_eventuallyEq ?_
  have h_chart_eq : ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀ :=
    chartAt_eventually_eq_of_locallyConstant b₀
  have h_chart_src : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    (chartAt H b₀).open_source.mem_nhds (mem_chart_source H b₀)
  filter_upwards [h_chart_eq, h_chart_src] with b hb_eq hb_src
  show continuousLinearMapAtFlat (I := I) (M := M) b₀ b = ContinuousLinearMap.id ℝ E
  show (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
    = ContinuousLinearMap.id ℝ E
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hb_src]
  have h_achart_eq : achart H b = achart H b₀ := Subtype.ext hb_eq
  rw [h_achart_eq]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b₀) b
    (by simpa [tangentBundleCore_baseSet] using hb_src) v

private theorem mfderiv_extChartAt_apply_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (b₀ : M) (v : E) :
    ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) b₀ := by
  have h_cLMA := continuousLinearMapAtFlat_contMDiffAt (I := I) (M := M) b₀
  have h_apply : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun b : M => continuousLinearMapAtFlat (I := I) (M := M) b₀ b v) b₀ :=
    h_cLMA.clm_apply contMDiffAt_const
  have h_base : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    (chartAt H b₀).open_source.mem_nhds (mem_chart_source H b₀)
  have h_eq : (fun b : M => continuousLinearMapAtFlat (I := I) (M := M) b₀ b v)
      =ᶠ[𝓝 b₀] (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) := by
    filter_upwards [h_base] with b hb
    show (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b v
      = mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hb]
    rfl
  exact h_apply.congr_of_eventuallyEq h_eq.symm

/-- **Math.** Constant-vector tangent section is smooth. For `v : E`, the section
`b ↦ ⟨b, v⟩` (with `v` viewed as fiber via `TangentSpace I b = E`) is
$C^\infty$. Used by `SmoothVectorField.const`. -/
theorem contMDiff_constSection_TangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (v : E) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, v⟩ : TangentBundle I M)) := by
  intro b₀
  set e := trivializationAt E (TangentSpace I) b₀ with he_def
  have h_he : (Bundle.TotalSpace.mk b₀ v : TangentBundle I M) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' (F := E) b₀
  refine (Bundle.Trivialization.contMDiffAt_iff (IM := I) (IB := I) (e := e)
    (f := fun b : M => (Bundle.TotalSpace.mk b v : TangentBundle I M)) (n := ∞) h_he).mpr ?_
  refine ⟨contMDiffAt_id, ?_⟩
  have h_base : e.baseSet ∈ 𝓝 b₀ :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' b₀)
  have h_eqOn : (fun b : M => (e ⟨b, v⟩).2)
      =ᶠ[𝓝 b₀] (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) := by
    filter_upwards [h_base] with b hb
    have hb' : b ∈ (chartAt H b₀).source := by
      rwa [TangentBundle.trivializationAt_baseSet] at hb
    show (e ⟨b, v⟩).2 = mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v
    rw [(Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hb v).symm,
        TangentBundle.continuousLinearMapAt_trivializationAt hb']
    rfl
  exact (mfderiv_extChartAt_apply_smoothAt (I := I) (M := M) b₀ v).congr_of_eventuallyEq
    h_eqOn

/-! ### Layer 2 — finite-dim continuous linear map lift -/

                                                                          
                                                                           
                                                                                
                                                
                                                             
               
                                                                                    
                                                           
                                                 
                                   
                                                                                           
          
       
                
                                                        
                     
              
                                
           
                                            
                                                                   
                   

                                                                                                   
                                                              
                                                             
                                                             
                                                           
                                                                      
                                                        
                                                                                    
                                                           
             
                                                 
                                             
                                                      
                                       
                                                
                                                       
                             
           
                                                           
                                                                             
                                                                                 
                                                                                            
                   
             
                                                 
                                                      
                                                     

                                                            

                                                       
                                                        
                                                                 
                                                                          
                                       
                      
                           
                                                                                         
                                                            
                                                                         
                                                                                            
                                                      
                                                                                            
                                   
                                                              
                                                           
                                      
                                                                           
                   
            
                                                                                

                                                     
                                                        
                           
                                                                 
                                                                          
                                       
              
                                   
                                                      
                                                            
                                                            
                                    
                                                     
                                                    
           
         
                                                            

                                             
                                                        
                           
                                                                 
                                                                          
                                       
             
                                         
                                                                                                           
                                              
                                                     
                                                        
                                           
                                       
                                                      
                                 
                                                   
                             
                                                           
                
                                                                      
                                   
                                    
                                                        
                                                              
                                   
                                
                               
                                                     
                                                    
                                                      
                
                                                                      
                                   
                                                                            
                                      
                                                                         
                                              
                                                                         
                                               
                                                             
                                            
                                                      
                                      
                                   
                
                                                                  
                                                   
                         
                                                          
                                                                   
                                                                      
                                                                                             
                            
              
                                                                     
                                 
                                                                                  
                                                                          
                                     
                                       
                     
                                                                              
                                                                             
                                                                        
                                  
                                                                     
                                                                          
                   
                                                                                             
                                                                                              
                                                              

                                                         
                                                        
                           
                                                                 
                                                                          
                                       
             
                                                   
                                                                                                                    
                                                        
                                                       
                                                                                                        
                                                                     
                                                                    
                                                                                                         
                                    
                                                                               
                                                        
                                                        
                                                                 
                                                                          
             
                                                  
             
                                                                                                                   
                                                   
                                                             
                                         
                                                          
                                                                                  
                                               

                                                                      
                                                                 
                                   
                                                        
                           
                                                                 
                                                                          
                                       
             
                                       
                                                            
                                                                  
                                                       
                                                                             
                                                                                        
                                   
                                                                          
                        
                                 
                                                                    
               
                                         
                              
                                                           
                                                                                                             
                   
                                                                     
                                                   
                                                                                                                  
                                            
                                    
                                                                  

end TangentBundle
