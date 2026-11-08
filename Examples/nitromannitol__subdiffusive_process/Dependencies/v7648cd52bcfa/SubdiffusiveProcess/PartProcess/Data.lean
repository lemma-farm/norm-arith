module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.Processes.E7.Leaves
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.Processes.E7.ResolventExists
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.KilledCoreClosure
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.FOTProduct
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.MarkovProcess.Trajectory.FeynmanKacFunctional
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
/-- Precisely the form/process hypotheses of the part-process statement. -/
structure Data (d : ℕ) (m : Measure (Fin d → ℝ)) where
  form : _root_.SubdiffusiveProcess.DirichletForm m
  regular : _root_.SubdiffusiveProcess.DirichletForm.IsRegular form.toClosedForm
  semigroup : SubMarkovKernelSemigroup (Fin d → ℝ)
  conservative : semigroup.IsConservative
  feller : semigroup.IsFellerKernelSemigroup
  law : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))
  markov : IsMarkovKernel law
  marginals : ∀ I x, law.map (ContinuousPath.finsetEvaluation I) x =
    SubMarkovKernelSemigroup.finiteSetKernel semigroup I x
  associated : ∀ (α : ℝ), 0 < α →
    ∀ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m,
      _root_.SubdiffusiveProcess.DirichletForm.IsResolvent form.toClosedForm α G →
      ∀ (g : (Fin d → ℝ) → ℝ) (_hg : Continuous g) (_hgc : HasCompactSupport g)
        (hgL : MemLp g 2 m),
        (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
          ∫ w, g (w (Real.toNNReal t)) ∂(law x)) =ᵐ[m] ⇑(G (hgL.toLp g))
end SubdiffusiveProcess.PartProcess
