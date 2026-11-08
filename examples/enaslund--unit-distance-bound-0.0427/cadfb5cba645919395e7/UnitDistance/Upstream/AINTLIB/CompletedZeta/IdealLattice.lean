/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
Modified for enaslund/unit-distance-bound: import lines relocated from
DedekindResidue.* to UnitDistance.Upstream.AINTLIB.* and `public import Mathlib`
narrowed to specific Mathlib modules for the Lean 4.32.0 / Mathlib 81a5d257 pin;
proof text unchanged. Upstream and local hashes: third-party/aintlib/manifest.json.
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Tactic
public import UnitDistance.Upstream.AINTLIB.CompletedZeta.ThetaLattice

/-!
# Ideal lattices in Euclidean coordinates  (SP1-AGE-1)

The theta/Poisson layer (`ThetaLattice.lean`) lives on `EuclideanSpace ℝ ι`. Hecke's
construction sums Gaussians over the images of (fractional) ideals of `K` under the mixed
embedding. This file transports mathlib's ideal lattices into that Euclidean frame:

* `mixedEmbedding.idealLattice K I ⊂ mixedSpace K` (mathlib) is pulled back along the
  continuous linear equivalence `euclidean.toMixed K` to
  `euclideanIdealLattice K I ⊂ euclidean.mixedSpace K` — mirroring mathlib's own
  `euclidean.integerLattice` — and then along the orthonormal-basis coordinate isometry
  `(euclidean.stdOrthonormalBasis K).repr` to `idealZLattice K I ⊂ EuclideanSpace ℝ (index K)`.
* Both transports are measure-preserving, so the covolume is mathlib's
  `covolume_idealLattice`: `covol = N(I)·2^{-r₂}·√|Δ_K|` (`covolume_idealZLattice`).

The `ZLattice` instances come from `ZLattice.comap`. Everything is genuine; no stubs.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The ideal lattice of a fractional ideal `I`, in the Euclidean mixed space — the pullback
of mathlib's `mixedEmbedding.idealLattice` along `euclidean.toMixed` (mirroring mathlib's
`euclidean.integerLattice`). -/
noncomputable def euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (euclidean.toMixed K).toLinearMap

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (euclideanIdealLattice K I) := by
  exact inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (euclidean.toMixed K).toLinearMap))

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (euclideanIdealLattice K I) := by
  exact inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (mixedEmbedding.idealLattice K I)
    (euclidean.toMixed K).toLinearMap))

open scoped Classical in
/-- The ideal lattice of `I` in coordinates: the pullback of `euclideanIdealLattice` along
the orthonormal coordinate isometry, as a lattice in `EuclideanSpace ℝ (index K)` — the
frame in which the theta/Poisson layer (`thetaLattice`, `weightedThetaLattice_transform`)
applies directly. -/
noncomputable def idealZLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  ZLattice.comap ℝ (euclideanIdealLattice K I)
    ((euclidean.stdOrthonormalBasis K).repr.symm.toContinuousLinearEquiv).toLinearMap

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (idealZLattice K I) := by
  exact inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (euclideanIdealLattice K I)
    ((euclidean.stdOrthonormalBasis K).repr.symm.toContinuousLinearEquiv).toLinearMap))

open scoped Classical in
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (idealZLattice K I) := by
  exact inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ (euclideanIdealLattice K I)
    ((euclidean.stdOrthonormalBasis K).repr.symm.toContinuousLinearEquiv).toLinearMap))

                        
                                                                        
                                                                           
                                                                           
                                                                  
                                                
                                                                
                                                                 
                                            
                                   
                                                                      
                                                                         
                          

open scoped Real

                        
                                                                                          
                                                                                       
                                                                                       
                                                                             
                                                                             
                                    

                        
                                                                             
                                                                                      
                                                                                            
                       
                                                                                     
                    
                                                                 
                                                                
                                                   
                                                                     
                                                                                        

                        
                                                                                             
                                                                                          
                                                                                          
                           
                                                                         
                                                                                          

                        
                                                     
                                                                          
                      
                                                          
                                                         
                                                      
                                                                        
        
                                                    

                        
                                                                                
                                                                     
                                                                                

                        
                                                                                          
                                                                                       
                                                                                          

                        
                                                                                          
                                                                                       
                                                                                          

                                                                                            
                                                              
                                                 
                                                            

                       
                                                                  
                     
                             
                                             

                                    
                        
                                                                                            
                                                                                         
                                    
                                                   
                                                                                     
                                                                        
                                                                                  
                                                                 
                                                                  
       
                                                                                       
                                    
                 
                                                                    
                       
                                              
                                                 
         
                            
                                               
                                                                       
                                                                           
                                                  
                           
                                                            
                                                           
                                               
                                                             
                     
        
                                                        
                                                     
                                               
                                           
                                                                        
                                              
                                                          
                                                         
                           
                                                                        
                                              
                                                           
                                                         
                           
                                                                               
                                                                     
                                        
                                                                         
        

                        
                                                                                            
                                    
                                                                                              
                         
                                                                           
                                           
                                                              
                                                                            
             
                       
                      
                        
                                                             
                                                                                                   
              
          
           
        
                       
                      
                        
        

                                                                     
                                                                     
                                                                     
                                             
                                                
                                                 
                                                           

                                                                             
                                                           
                                                                   
                                  
                                                                     
                                                        

                                                                    
                                                                                       
                                                                 
                                                                                
                                 
                                                                  
                                            
                                                                  
                                                                                            
       
                                                     
                                                                       
                                                                                   
                                                     
                                                                                          
                                             
                               
                                                                             
                                                                               

                        
                                                                                     
             
                             
                                                                            
                            
                                                                                             
                                             
                         
                                          
                                                       
                                                                 
           
                          
                         
            
                                                                                  
      

                                              
                                                                                            
                                                                                         
                                                                 
                                                          
                                      
                                                                               
                                              
            
                                                                               
                            
                           
                                                                          
                                 
            
                                                                      
                                                                        
                                     
                       
            
                              
                           
                                                               
                                                                     
                                                                        
                                         
                       
                        
                
           
     

                        
                                                                                            
                                                                                           
                                                                                            
                                                   
                                                                           
                                                                      
                                    
                                                              
                                        
                                                                                       
                                                                          
                                                      
                                                             
                                                                      
                                                                      
                                   
                                               
                                                                        
                                                                       
                                                                     
                                                                          
                                                                             
                                                         
            
           
                                                          
                                                            
                                        
                                                                                   
                         
                                                 
        
                                                
                         
                                                                                        
                        
                                                      
                      
                
                                  
                                                                          
                                                                     
                                                                          
              
                                        
                                   
                                                                                       
                                     
                                                                  
                                                             
           
                  
            
         
                                                                                 
                         
          

end

end DedekindResidue
