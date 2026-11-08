module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Sampling.Ingham
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Atomic.GramSchur
public import Mathlib
@[expose] public section
/-!
# Cosine-window finite Ingham inequality

This module proves a separated-frequency Ingham lower bound at the strict
threshold `2ad > 1`. A cosine taper turns the window kernel into an explicit
reciprocal-quadratic kernel. Rounding scaled differences toward zero embeds
each off-diagonal row into integer shells, whose exact telescoping sum is one;
a finite Schur estimate then supplies the positive lower quadratic floor.
-/
namespace MeyerGeneralProblem
open Filter MeasureTheory ComplexConjugate
noncomputable section
end
end MeyerGeneralProblem
