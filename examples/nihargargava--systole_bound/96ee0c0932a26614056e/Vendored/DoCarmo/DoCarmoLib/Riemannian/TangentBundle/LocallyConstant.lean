module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/TangentBundle/LocallyConstant.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000


/-!
# Locally constant charted space

The `IsLocallyConstantChartedSpace` typeclass: in every neighbourhood of
every basepoint, `chartAt H` is constant. Standard Mathlib examples
(Euclidean spaces, single-chart-per-region atlases) satisfy this. The
class is needed because Mathlib's `ChartedSpace` only requires local
compatibility of chart *transitions*, not local constancy of the
chart-selection function `chartAt H : M → PartialHomeomorph M H` —
without local constancy, parametric chart-derivatives are not
generally smooth.

Plus a strict-interior nbhd-propagation lemma consumed by the Bochner
stack (`extChartAt_self_eventually_mem_closure_interior_range`).
-/

open scoped Manifold Topology

/-- A charted space has locally constant chart selection if, near every base point, `chartAt H`
chooses the same partial homeomorphism as it does at the base point. -/
class IsLocallyConstantChartedSpace
    (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  /-- `chartAt H b = chartAt H b₀` eventually as `b → b₀`. -/
  chartAt_eventually_eq : ∀ b₀ : M, ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀

theorem chartAt_eventually_eq_of_locallyConstant
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsLocallyConstantChartedSpace H M] (b₀ : M) :
    ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀ :=
  IsLocallyConstantChartedSpace.chartAt_eventually_eq b₀

/-- **Eng.** `H` over itself satisfies `IsLocallyConstantChartedSpace`
(charts are constantly `PartialHomeomorph.refl H`). -/
instance instIsLocallyConstantChartedSpace_self
    (H : Type*) [TopologicalSpace H] :
    IsLocallyConstantChartedSpace H H where
  chartAt_eventually_eq _ := Filter.Eventually.of_forall (fun _ => rfl)

                                                                                    
                                                                              
                                                              
                                                  

                                                                         
                                                                            
                                                                         
                                                                   
                                                                     
                                                                      

                                                                    
                                                                  
                                                                     
                                                             
                                           
                                                        
                                                                 
                                                       
                                               
                                                            
                                                                          
                                                               
                                                             
                                              
                                                                    
                                         
                                   
                                                                          
                                                                              
                                                                             
                                                          
                                         
                                                                                    
                                                                       
                                                            
             
                             

