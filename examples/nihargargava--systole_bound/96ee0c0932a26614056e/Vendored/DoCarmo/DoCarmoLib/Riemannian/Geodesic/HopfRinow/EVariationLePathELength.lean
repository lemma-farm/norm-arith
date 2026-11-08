module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Vendored.DoCarmo.Shared.MetricGeometry.LengthSpace

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false

/-!
# Metric variation is bounded by Riemannian path length

For a `C¹` path, the metric `eVariationOn` (and hence OpenGA's
`pathLength`) is bounded by the tangent integral `Manifold.pathELength`.

Proof map (do Carmo Ch. 7 §2 / Burago–Burago–Ivanov §2.7.1):
```
eVariationOn (↑γ) univ = ⨆_partitions  Σ edist (γ tᵢ₊₁) (γ tᵢ)
  ≤ ⨆_partitions Σ pathELength I γ.extend tᵢ tᵢ₊₁   -- edist = riemannianEDist ≤ pathELength
  = pathELength I γ.extend 0 1                        -- pathELength_add telescoping
```

-/

open Bundle Set Topology
open scoped Manifold ContDiff

namespace OpenGA.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- **Math.** Per-segment bound: on a `C¹` path, the metric distance between two
parameter values is bounded by the tangent-integral length over that subinterval.
`edist (γ a) (γ b) = riemannianEDist ≤ pathELength I γ a b`. -/
theorem edist_le_pathELength_of_cmdiff {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ) (hab : a ≤ b) :
    edist (γ a) (γ b) ≤ Manifold.pathELength I γ a b := by
  rw [IsRiemannianManifold.out (I := I) (γ a) (γ b)]
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

                                                                                   
                                                                                   
                         
                                               
                                
                                                                 
                                                                            
                                                                                 
                                                                               
               
                           
                                                                            
                                                                                                    
           
                   
                                        
                                                                                 
                                                                               
                                                                                   
                                                  
           
                    
                  
                  
                                    
                                                                                   
                                                            
                                                                           
                                         
                                                      
                                                                                   

end OpenGA.HopfRinow
