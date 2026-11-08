module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/TensorBundle/SmoothOrthoFrame/ChartBasis.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream package-option restoration, and pinned API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Metric.RiemannianMetric

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream independent metric binders rather than changing theorem contracts.
set_option linter.overlappingInstances false


/-!
# Chart-basis tangent sections and the un-normalised $g$-Gram-Schmidt

Construction-only Foundation for `Tensor/SmoothOrthoFrame.lean`:

* **Stage 1** — `chartBasisVecFiber α i b` transports the $i$-th
  model-space basis vector through the inverse of the tangent
  trivialization centred at $\alpha$, smooth on the base set and junk
  off it; `chartBasisVec`, `chartBasisFamily`, plus the linear-
  independence of the chart-basis family.
* **Stage 2** — fiberwise $g$-Gram-Schmidt: `chartFrameRawFiber` (the
  un-normalised vector), `chartFrameNormFiber` (the normalised vector),
  `chartFrameNorm` (the section-form package). Includes the basic
  recurrence identities (`chartFrameNormFiber_eq`,
  `chartFrameRawFiber_at_zero`, `chartFrameNormFiber_at_zero`,
  `g_inner_normalised`, `chartFrameNormFiber_at_zero_norm`).

Stage 3a's orthonormality proof lives in
`Tensor/SmoothOrthoFrame/Orthonormality.lean`; Stage 6's smoothness
chain lives in `Tensor/SmoothOrthoFrame/Smoothness.lean`. Anchor
`Tensor/SmoothOrthoFrame.lean` imports both and packages the public
`smoothOrthoFrame` + `OrthonormalBasis` API.
-/

noncomputable section


open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 1: chart-basis tangent sections -/

/-- **Math.** The $i$-th pointwise tangent vector of the chart-local
frame attached to $\alpha$: image of the $i$-th model-space basis vector
under `(trivializationAt E (TangentSpace I) α).symm b` on the base set,
junk off it. Smooth on `(chartAt H α).source`. -/
def chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    TangentSpace I b :=
  (trivializationAt E (TangentSpace I) α).symm b ((Module.finBasis ℝ E) i)

/-- **Math.** Section-form packaging of `chartBasisVecFiber α i` as
`M → TotalSpace E _`. -/
def chartBasisVec (α : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun b => TotalSpace.mk' E b (chartBasisVecFiber (I := I) α i b)

                                                             
                                
                                                    
                                                  

                                                             
                               
                                                    
                                                                               

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** On the base set, the trivialization sends the chart-basis
vector to the constant model-basis vector. -/
lemma trivializationAt_chartBasisVec_snd
    (α : M) (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (trivializationAt E (TangentSpace I) α
        ⟨b, chartBasisVecFiber (I := I) α i b⟩).2
      = (Module.finBasis ℝ E) i := by
  have h := (trivializationAt E (TangentSpace I) α).apply_mk_symm hb
    ((Module.finBasis ℝ E) i)
  simpa [chartBasisVecFiber] using congrArg Prod.snd h

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart-basis tangent-bundle section is smooth on the
base set of the trivialization at $\alpha$. -/
lemma chartBasisVec_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) α i)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) α)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun b => chartBasisVecFiber (I := I) α i b)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (Module.finBasis ℝ E) i)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro b hb
  exact (trivializationAt_chartBasisVec_snd (I := I) α i hb)

/-- **Math.** The chart-basis family at $b \in \mathrm{baseSet}$ is a
basis of `TangentSpace I b`, obtained by transporting the fixed
model-space basis through the trivialization. -/
def chartBasisFamily (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
  (Module.finBasis ℝ E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb).symm)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartBasisFamily_apply (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) α hb i =
      chartBasisVecFiber (I := I) α i b := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart-basis family is linearly independent at each
base-set point. -/
lemma chartBasisFamily_linearIndependent (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) := by
  have h := (chartBasisFamily (I := I) α hb).linearIndependent
  have hcongr :
      (chartBasisFamily (I := I) α hb : Fin (Module.finrank ℝ E) → TangentSpace I b)
        = fun i => chartBasisVecFiber (I := I) α i b := by
    funext i
    exact chartBasisFamily_apply (I := I) α hb i
  rw [← hcongr]
  exact h

/-! ## Stage 2: hand-rolled $g$-Gram-Schmidt of the chart frame, fiberwise

For a fixed point $b : M$, we recursively build the orthonormalised
basis `chartFrameNormFiber g α b i ∈ T_bM`, with
$i : \mathrm{Fin}\,(\mathrm{Module.finrank}\,\mathbb{R}\,E)$.

The recursion uses Lean's well-founded recursion on `i.val`: each step
references earlier fiber-values, and termination is by strict decrease
of the index. -/

                                                                                
                                                           
                                     
                                              
                                                        
                                                               
                               
                        
                  
                                    
                                               
                                 
                                         
                                         
                    
                          

                                                             
                                           
                                
                                      
                                                                
                                      

                                                                                 
    
                                                                                         
                                                              
                                                            
                                    
                                              
                                                        
                                     
                    
                                                    
                                             
                                               
                                          
                                         

                                                             
                                                                       
                                                                  
                            
                                              
                                    
                                          
                           
                                               
                                                     
                                                 
                                               
     

                               
                                                                                 
                                                          
                                
                                                
                                                         
                                                             
                           
      

                               
                                                                           
                                              
                                 
                                                
                                                          
                
                    
                                                               
                                                                     
                                                               
                                                         

                                                                                     
                                                                           
                                                        
                                                                                     
                                                    
                                                                                  
                       
                        
                                                             
                                
                                                 
                                                           
                                                    
                                                                  
                                                                           
                                                                                                          
                                                                                              
                                                                   
                                                                         
                                                                  
                      
                                    
                                                       
                                         
                                    
                                                      
                                                          
                                                          
                                     

                               
                                                                         
                                        
                                      
                                              
                                                                
             
                                                              
                                                                        
                                  
              
                                                              
                                                                
                                                           

end Tensor
end Riemannian
