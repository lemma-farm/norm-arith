module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/InitialVelocity.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Homogeneity
public import Mathlib
@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false



/-!
# Initial velocity and the geodesic equation at the initial time

For a geodesic witness with initial data `(p, v)` — a base curve `γ` lifted to an
integral curve `f` of the chart-`p`-fixed geodesic spray with `f 0 = ⟨p, v⟩` — we
extract the *analytic* content of the initial datum:

* `IsGeodesicOnWithInitial.hasDerivAt_extChartAt_zero` — read in the chart at
  `p`, the curve `γ` has derivative `v` at `t = 0`: the geodesic really leaves
  `p` with velocity `v`.
* `IsGeodesicOnWithInitial.hasGeodesicEquationAt_zero` — `γ` satisfies the
  intrinsic (moving-foot) geodesic equation `HasGeodesicEquationAt g γ 0` at the
  initial time. This bridges the spray/integral-curve formulation of geodesics
  back to the second-order geodesic equation of
  \S`Geodesic/Equation.lean`, at the initial time.

The mechanism: the tangent-bundle chart of `TM` at `f 0 = ⟨p, v⟩` is based at the
foot `p`, so mathlib's chart reading of the integral-curve property
(`IsMIntegralCurveAt.eventually_hasDerivAt`) is exactly the first-order system

`(x'(s), w'(s)) = (w(s), -Γ_p(w(s), w(s))(x(s)))`

for the pair `x = φ_p ∘ γ`, `w = ` chart-`p` fibre coordinate of `f`: the
`tangentCoordChange` appearing in the chart reading is precisely the
trivialization of `T(TM)` at `⟨p, 0⟩`, under which the spray reads as its
coordinate fibre value (`trivializationAt_apply_geodesicVectorFieldChart`).

Under the chart-validity clause of `maximalGeodesic_structure_of_footInSource`,
the same statements transfer to the canonical maximal geodesic
(`hasDerivAt_extChartAt_maximalGeodesic`,
`hasGeodesicEquationAt_maximalGeodesic_zero`), via agreement of witnesses
(`maximalGeodesic_eq_witness`).
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section CoordinateBridges

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The chart-`α` fibre coordinate of a tangent vector attached at `α`
itself is the vector: the trivialization at a point is the identity on the fibre
over that point. -/
lemma chartFiberCoord_mk (α : M) (w : TangentSpace I α) :
    chartFiberCoord (I := I) α (⟨α, w⟩ : TangentBundle I M) = w := by
  have h : chartFiberCoord (I := I) α (⟨α, w⟩ : TangentBundle I M) =
      tangentCoordChange I α α α w := rfl
  rw [h]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source α)

                                                                                                      
                                                                                     
                                                                               
                                                                        
                                                             
                                                               
                                                      
                                          
                                                                              
                                                             
                                        
                                                                        
                                                               
                                                                          
        
                                                                          

                                                                              
                                                                               
                                                                              
                                                                                  
                                                                              
                                                                        
                                                                                   
                                                                              
                                                          
                                                                 
                                                                        
                                                                              
               

omit [I.Boundaryless] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The coordinate change from the chart of `TM` at a point `q` to the
chart at the basepoint (any point with foot `α`) sends the definitional
presentation of the chart-fixed geodesic spray to its coordinate fibre value. -/
lemma tangentCoordChange_geodesicVectorFieldChart
    (g : RiemannianMetric I M) (α : M) (w₀ : TangentSpace I α)
    {q : TangentBundle I M} (hq : q ∈ geodesicChartDomain (I := I) α) :
    tangentCoordChange I.tangent q (⟨α, w₀⟩ : TangentBundle I M) q
        (geodesicVectorFieldChart (I := I) g α q) =
      geodesicVectorFieldChartFiber (I := I) g α q := by
  have h : tangentCoordChange I.tangent q (⟨α, w₀⟩ : TangentBundle I M) q
        (geodesicVectorFieldChart (I := I) g α q) =
      (trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨α, (0 : E)⟩ : TangentBundle I M)
        (⟨q, geodesicVectorFieldChart (I := I) g α q⟩ :
          TangentBundle I.tangent (TangentBundle I M))).2 := rfl
  rw [h, trivializationAt_apply_geodesicVectorFieldChart (I := I) g α hq]

end CoordinateBridges

section EventualSystem

variable [I.Boundaryless]

                                                                              
                                                                               
                                                                              
                                                        
                                                                     
                                                                 
                                                     
                                              
                                                             
                               
                                              
                                                                             
                                 
                                                                                
                                                                
           
                                        
                 
                                                    
                                                                           
                                                                        
                                                                         
              
                                                                  
                                    
                                              
                                                                  
                                                          
                                                                                   
                                                     
                                                         
                                                                    
                 
                                                                                
                       
                                                                              
                                     
                                                                        
                    
                                                   
                                                                             
                                          

end EventualSystem

section InitialData

variable [I.Boundaryless]

                                                                              
                                                                                 
                                                                           
                                                        
                                                          
                                                              
                          
                                                                            
                                                        
           
                                    
                                                                              
                              
                                                                       
                     
                                                                               
                                                          
                                                                        
                                           
            
                                                           
                
                   
                                             
                                                                  
                                                                 
            
                                                                    
                                         
                   
            

                                                                              
                                                                                   
                                                                             
                                                                             
                                                                   
                                                                          
                
                                                          
                                                              
                          
                                                                            
                                              
           
                                      
                                    
                                                                              
                              
                                                                           
                                              
                                                            
                                                                        
                                                        
                           
                                                                        
                                 
            
                                                                     
                
                      
                                                     
                                                            
                                  
                                                                            
              
                                                                     
                         
                                                                    
                               
                                                                            
              
                                                          
                                                      
            
                                                        
               
                                    
                              
                                             
            
                                         
                              
                                                                                  
                    
               
                              
                         
                                 
               
                                    
                          
                             
               
                                                  
                                      
                    
                                             
                                 
                                                               
                                                      
                                      
                                                                      
                                                                               
                                                                   
              
                                                     
                                                                   
                                                                   
                                                                  
                                          
                     
                          

end InitialData

section EquationCongruence

                                                             
                                                                                     
                                                             
                                                   
                                                      
                                                                       
                                               
                                    
                                            
                                                   
                                         
                                  
                                                                
                
                                                             
                                                         
                               
                                       
                                                                   
                                                             
                                                          
            
                                        
                                           
             

end EquationCongruence

section MaximalGeodesicTransfer

variable [I.Boundaryless] [T2Space (TangentBundle I M)]

                                                             
                                                                                 
                                                                           
                                                                      
                                                               
                                  
                                                             
                                        
                                                    
                                              
                             
                                                        
                                                                   
                           
                                                 
           
                                                           
                                   
                                           
                                           
                                                       
                                                           
                    
                                                               
                                                  
                                                       
                     

                                                             
                                                                                
                                                   
                                            
                                                             
                                        
                                                    
                                                
                                                                               
                                                                            
           
                                                            
                                       
                                                     
                                           
                                             
                                                                   

                                                             
                                                                                   
                                                                               
                                                     
                                             
                                                             
                                        
                                                    
                                                
                                                                                     
                                   
                                                      
                                                        
                                    
                                
         

                                                             
                                                                               
                                                                   
                       
                                                  
                                                             
                                        
                                                    
                                                
                                                                             
                                   
                                                      
                                                        
                                                                   

end MaximalGeodesicTransfer

end Geodesic
end Riemannian

end
