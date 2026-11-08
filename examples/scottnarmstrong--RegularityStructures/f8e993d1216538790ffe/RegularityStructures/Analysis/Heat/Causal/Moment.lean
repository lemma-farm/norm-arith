/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Causal.Basic
public import RegularityStructures.Analysis.Heat.Annihilating.Moment
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# The causal shells annihilate polynomials

`∫ z^k annShellC N n z dz = 0` for `|k|_𝔰 < N` (`integral_monomial_mul_annShellC`) and
`annihilatesPolynomials_annShellC N : AnnihilatesPolynomials (fun n x y => annShellC N n (x - y)) (N - 1)`
[Hai14, Assumption 5.4].  Same proofs as for the non-causal shells.

Source: Hairer, arXiv:1303.5113v4, Lemma 5.5 and Assumption 5.4.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

                                                     
                                                                                       
                                 

                                                                   
                                                 
                                                                                        
                            
                                                                                              
                                                                                 
                                                                                    
                                                                                 
                                                   
                           
            
                                                  
                                                                  
                                                                  
                             
               
                                        
                               
                                   
                                              
                                                                
                                                                                 
         
                                                    
                                                                 
                                                 
                                          
                                                                           
            
                                                                           
                    
                                                         
                               
                                                                                          
                                            
                       
              
        
         
          

end RegularityStructures

end
