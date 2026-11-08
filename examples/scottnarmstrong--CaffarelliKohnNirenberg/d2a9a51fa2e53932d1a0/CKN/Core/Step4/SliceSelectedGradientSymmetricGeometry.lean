-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.Step4.SliceSelectedGradient
import CKN.Foundation.Parabolic.BallDisplays

/-! # Geometry of the symmetric parabolic window

Display `eq:parabolic-ball` of `paper/ckn.tex` presents the parabolic ball of
radius `R` about `z₀ = (x₀, t₀)` as the product of the spatial Euclidean ball
`B_R(x₀)` with the symmetric time interval `(t₀ - R², t₀ + R²)`, written
`𝔅_R(z₀)`.

This file records the elementary spatial facts needed to rewrite membership
between the one-sided and symmetric carriers: the explicit round ball
`euclideanBall` is the norm ball `vec3Ball`, and the closure of a smaller norm
ball lies inside any larger one, so the boundary of an inner carrier is
absorbed by the slightly larger open window used in display (3.5).

The module contains no analytic content: it is pure parabolic geometry, and its
statements are used only to rewrite membership between the one-sided and
symmetric carriers. -/

open MeasureTheory Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN.Core.Step4

                                                                                
                                                                             
                                                                         
                                              
                                                                           
                                            
       
                                                                 
                                                                             

                                                                             
                                                                               
                                                                             
                                                     
                                                                          
                   
                                               
                          
            
                                      
                             

end CKN.Core.Step4
