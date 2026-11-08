module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Metric/RiemannianMetric.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream package-option restoration, and pinned API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Vendored.DoCarmo.Shared.Algebraic.BilinearForm.Basic
public import Vendored.DoCarmo.Shared.Algebraic.BilinearForm.Riesz
public import Vendored.DoCarmo.Shared.Util.Attributes

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000

/-!
# Riemannian metric

A smooth, symmetric, positive-definite tensor field $g$ on $M$ assigning
an inner product $g_x : T_xM \times T_xM \to \mathbb{R}$. In DoCarmoLib,
`RiemannianMetric I M` aliases Mathlib's
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` — i.e., *data*
(structure inhabitant), not a typeclass. Operators take `g` as an
explicit argument; multiple metrics on the same manifold coexist.

Provides `g.metricInner` (bilinear-form algebra), `g.metricRiesz` (Riesz
duality $(T_xM)^* \to T_xM$), their smoothness, and bridge instances on
`TangentSpace I x` (NormedAddCommGroup, InnerProductSpace, FiniteDimensional, CompleteSpace).

Reference: do Carmo §1.2; Lee, *Smooth Manifolds*, Ch. 13.
Mathlib upstream: `Mathlib.Geometry.Manifold.VectorBundle.Riemannian`.
-/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace Riemannian

/-! ## The metric type -/

/-- **Math.** A **Riemannian metric** on a smooth manifold $M$ modelled
on $(E, H, I)$. Mathlib's `Bundle.ContMDiffRiemannianMetric` aliased:
data, not a typeclass attribute. -/
abbrev RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

/-- **Math.** **`[HasMetric I M]` typeclass**: thin wrapper around
`RiemannianMetric I M` to make the metric instance-bindable when
downstream code binds `{I : ModelWithCorners ...}` independently of
the manifold's bundled `modelI`. Single-field class; bridged from
`[RiemannianManifold M]` in `Manifold.lean`. -/
class HasMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    where
  /-- The Riemannian metric on $(M, I)$. -/
  metric : RiemannianMetric I M

/-- **Eng.** Bridge: `[HasMetric I M]` induces a global
`Bundle.RiemannianBundle (TangentSpace I : M → Type _)`, activating
Mathlib's scoped `NormedAddCommGroup` and `InnerProductSpace ℝ`
instances on each fibre. Single `NormedAddCommGroup` / `InnerProductSpace` source. -/
noncomputable instance instRiemannianBundleOfHasMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [hm : HasMetric I M] :
    Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
  ⟨hm.metric.toRiemannianMetric⟩

end Riemannian

namespace Riemannian.RiemannianMetric


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Inner product -/

/-- **Math.** The **metric inner product** $\langle V, W\rangle_g = g_x(V, W)$. -/
noncomputable def metricInner (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) : ℝ :=
  g.inner x V W

@[simp]
theorem metricInner_apply (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V W = g.inner x V W := rfl

                                                                           
                                                   
                                      
                                                
              

                                                                                        
                                                       
                                                 
                              
              

              
                                                       
                                          
                                                                                   
                                                              
                               

              
                                                        
                                          
                                                                                
                             

              
                                                        
                                              
                                                             
                                              
                                

              
                                                         
                                              
                                                             
                                              
                                  

              
                                                        
                                    
                                 
                        
                                

              
                                                         
                                    
                              
                        

              
                                                       
                                      
                                                       
                                        
                               

              
                                                        
                                      
                                                    
                         

              
                                                       
                                          
                                                                                   
                                                              
                               

              
                                                        
                                          
                                                                                
                             

                                                           
              
                                                          
                                    
                                 
                                  
                                    
                                                  

end Riemannian.RiemannianMetric

/-! ## TangentSpace fibre instances

`NormedAddCommGroup`, `NormedSpace`, and `InnerProductSpace` on each
fibre `TangentSpace I x` are *not* declared here. Instead, they are
supplied by Mathlib's scoped `Bundle.RiemannianBundle`-derived
instances, which become active once a `RiemannianBundle E` is in scope
(e.g., via the global instance on `[RiemannianManifold M]`, or via a
local `letI`). Routing through `RiemannianBundle` ensures that the
inner product the Mathlib `inner` projection lands on is *exactly*
`g.inner b · ·`, sidestepping the lean4#13063 `NormedAddCommGroup` diamond.

The non-metric fibre instances `FiniteDimensional` and `CompleteSpace`
are orthogonal to the `NormedAddCommGroup` / `InnerProductSpace` chain and are transported here via the
`TangentSpace I x = E` def-eq. -/

namespace Riemannian

section TangentSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance instFiniteDimensionalTangent [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) := by
  show FiniteDimensional ℝ E
  infer_instance

end TangentSpaceInstances

end Riemannian

/-! ## Riesz duality

In a finite-dim inner product space $V$, every continuous linear functional
$\varphi : V \to \mathbb{R}$ is uniquely represented as $\langle V_\varphi, \cdot\rangle_g$. -/

namespace Riemannian.RiemannianMetric


section Riesz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

                                                                     
                                          
                                                                  
                            
                 
                              
                      
                                                                       
                                                   
                    
                                                         
                                                   
                                                
                                             

                               
                                                                 
                                                 
            
                        
                    

                                                         
                                                                   
                                                        
           

                               
       
                                                             
                              
                                                     

                               
                                                                   
                                               
               
                                                                
       
                                      
                                                              

                               
                                                                                                
                                                                
                              
                                                                                  
                                                             

                                                                                                   

                                                                      
                                                     
                                                                
                                    
                       
                                               
                                    

                                                                                                            
                                                            
                                                           
                                                  
                                                     
                                      

                                                                                                  
                                                             
                                                         
                                          
                            
                                                        
                                      

                                                                   
                                               
                                         
         
                                
       
                                 

                                                                               
                                                           
                                                                         
                        
                                                                        
                                                        
                                                                                     

end Riesz

end Riemannian.RiemannianMetric

/-! ## Smoothness of the metric inner product — Math headline

`g_y(v(y), w(y))` is `ContMDiffWithinAt` whenever the tangent-bundle
sections `v, w` are. The pointwise / set / global parity variants and
the first-order `MDifferentiable*` analog family live in
`Riemannian/Util/MetricInnerSmoothness.lean`. -/

namespace Riemannian.RiemannianMetric

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {v w : ∀ x : M, TangentSpace I x} {s : Set M} {x : M}

variable {n : ℕ∞ω} [hLE : ENat.LEInfty n]

                                                                                   
                                            
                                     
                              
                                                
                                                    
                                                
                                                      
                                 
                                                      
                                                                    
                          
                                                         
                                                          
                                     

end Smoothness

end Riemannian.RiemannianMetric
