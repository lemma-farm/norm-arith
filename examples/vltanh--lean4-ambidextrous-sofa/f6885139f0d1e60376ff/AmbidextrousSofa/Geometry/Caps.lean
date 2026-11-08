module

public import AmbidextrousSofa.Geometry.Plane

@[expose] public section

/-!
# Actual convex hulls and downward caps

`IsDownwardCap` describes the broad scalar domain: nonempty compact convex
sets in the unit strip, closed downward to the baseline. It permits subunit
height, zero width, asymmetry, and nonsmooth boundary.

`upperCap` fills vertically down from a set. The lemmas below establish its
elementary containment, projection, and fixed-point properties. Compactness,
convexity, support functions, and integral scores for hull-derived caps remain
separate formalization tasks.
-/

namespace AmbidextrousSofa

                                                           
                                                            

                                                                                 
def horizontalProjection (S : Set Plane) : Set ℝ := Prod.fst '' S

                                                                                 
                                           
                                                 

                                                                                 
structure IsDownwardCap (U : Set Plane) : Prop where
  nonempty : U.Nonempty
  isCompact : IsCompact U
  convex : Convex ℝ U
  inStrip : U ⊆ unitStrip
  downward : ∀ p ∈ U, ∀ y : ℝ, 0 ≤ y → y ≤ p.2 → (p.1, y) ∈ U

                                                                                     

                                                                                            

                                                                            
                                                                           
                                                                    
                                                 

                                                                  
                                                                                   
                                        

                                                                           
                                                                               
                                                                 
                                                                     
                                         

                                                                 
theorem IsDownwardCap.baseline_mem {U : Set Plane} (hU : IsDownwardCap U)
    {p : Plane} (hp : p ∈ U) : (p.1, 0) ∈ U :=
  hU.downward p hp 0 le_rfl (hU.inStrip hp).1

end AmbidextrousSofa
