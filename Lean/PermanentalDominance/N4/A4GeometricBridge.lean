import PermanentalDominance.N4.A4GeometricFourVector

/-!
# Geometric `A₄` certificate entry point

The direct Gram/geometric proof supplies `FourVectorProperty` without the
spectral `A4Gap` route, and the Schur argument turns it into certificate
positivity.
-/

noncomputable section

open Complex Matrix
open scoped ComplexOrder

namespace PermanentalDominance.N4.A4GeometricBridge

open A4Certificate A4Geometric

/-- Restored old-route entry point.  Its proof factors through the
four-vector/Schur interface rather than invoking the characteristic-polynomial
certificate directly. -/
theorem certificate_posSemidef_geometric {u v w : ℂ}
    (hB : IsPSD (A4Certificate.correlation u v w)) :
    IsPSD (certificate u v w) :=
  certificate_posSemidef_of_fourVector hB
    (A4GeometricFourVector.fourVectorProperty u v w)

end PermanentalDominance.N4.A4GeometricBridge
