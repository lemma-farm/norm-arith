-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Foundation
public import Mathlib.Analysis.LConvolution
public import Mathlib.Analysis.Convolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ}

/-- A dedicated subtraction carrier for the group convolution.
Only subtraction and measurable structure are supplied; no commutative group
law is asserted (BB Convention 3.43, Def 3.44, pp. 118–119). -/
def ConvolutionCarrier (_G : HomogeneousGroup N) := Fin N → ℝ

instance convolutionCarrierSub (G : HomogeneousGroup N) : Sub (ConvolutionCarrier G) :=
  ⟨fun x y => G.mul x (G.inv y)⟩
instance convolutionCarrierMeasurableSpace (G : HomogeneousGroup N) :
    MeasurableSpace (ConvolutionCarrier G) := inferInstanceAs (MeasurableSpace (Fin N → ℝ))
instance convolutionCarrierMeasureSpace (G : HomogeneousGroup N) :
    MeasureSpace (ConvolutionCarrier G) := inferInstanceAs (MeasureSpace (Fin N → ℝ))

                                                                 
                                                                          
                                                                           
                         
                                                         

                                                                
                                                                              
                                                                               
                                         
                                                                    
                                                
                                                                                                

                                                             
                              
                                                                            
                                                     
                                                   

                                                                   
                         
                                                                                 
                     
                                                                        

                                                            
                                                                            
                                                                            
                                             
                                                                     
                                               
                      

end RothschildStein.G2
