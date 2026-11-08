/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Feller.FiniteTimeJointCompactTestContinuity
import MarkovProcess.FiniteTime.FiniteSetKernelCompactTestTransport

/-!
# Continuity of finite-set compact-test integrals

Compact-test integrals against a conservative Feller semigroup's finite-set kernel vary
continuously with the starting point. The proof transports the test to increasing coordinates
and applies fixed-time finite-kernel continuity. The empty finite set is included without a
separate nonemptiness assumption.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

                                                                                               
                                                                                      
                                                                              
                                                                         
                                                                  
                                                                              
                                                         
                                                                                      
           

end MarkovProcess.SubMarkovKernelSemigroup
