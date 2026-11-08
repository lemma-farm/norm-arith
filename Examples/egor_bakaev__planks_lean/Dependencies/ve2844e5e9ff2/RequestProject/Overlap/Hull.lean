module
public import Examples.egor_bakaev__planks_lean.Dependencies.ve2844e5e9ff2.RequestProject.Overlap.Geometry
public import Mathlib
/-!
# The candidate hull `K₀ = conv(J_P ∪ J_Q)`

* every line meeting the hull meets one of the two chords;
* the hull lies in a strip of half-width `2ρ sin β` around `ℓ_P`, so `|K₀| ≤ 8ρ² sin β`;
* the hull contains a rectangle of size `1.2ρ × 0.11ρ sin β` next to `ℓ_P`
  (Lemma 4.6), so `|K₀| ≥ 0.132ρ² sin β`.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
end Annulus
end
