-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

import CKN.Core.HeatPotential.SubordinatedCampanato
import CKN.Statements.SuitableWeakSolutionIntegrable
import CKN.Setting.Energy.Calculus
import CKN.Pressure.LeibnizLaplacian

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

set_option autoImplicit false

noncomputable section

namespace CKN.Core.Step3

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

/-!
# Localized equation and heat-potential representation

The cutoff-tested S3 identity is the distribution-free entry point for the
local equation.  The source terms below are the paper's displayed formulas.
The pressure representation is recorded as a structural decomposition, while
the pointwise estimate is proved directly from the explicit heat kernels.
-/

                                              
                                                          
                    

                                                   
                                                                   
                                  

                                               
                                                                    
                                                          
                   
                             
                                                          
                                                      

                                               
                                                                  
                                              









end CKN.Core.Step3
