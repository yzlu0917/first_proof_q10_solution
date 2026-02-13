import autoproof.Q10.TraceAndRates.TraceModels

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Mainline preconditioner action bridge: both preconditioners are exact left inverses of
their model operators under SPD assumptions. -/
theorem q10_mainline_preconditioner_action_bridge
    (P : Problem n M r q)
    (hLam : 0 < P.lam)
    (hKpos : P.K.PosDef) :
    (∀ R : Matrix (Fin n) (Fin r) Real,
      (P.lam • ((1 : Matrix (Fin r) (Fin r) Real) ⊗ₖ P.K)) *ᵥ (precond1Apply P R).vec = R.vec) ∧
    (∀ R : Matrix (Fin n) (Fin r) Real,
      precond2Matrix P *ᵥ (precond2Apply P R).vec = R.vec) := by
  refine ⟨?_, ?_⟩
  · intro R
    exact precond1_correct_of_posDef (P := P) hLam hKpos R
  · intro R
    exact precond2_correct_of_posDef (P := P) hLam hKpos R

/-- Mainline preconditioner-2 closed-form and cost bridge. -/
theorem q10_mainline_precond2_closed_form_bridge
    (P : Problem n M r q)
    (hLam : 0 < P.lam)
    (hKpos : P.K.PosDef)
    (R : Matrix (Fin n) (Fin r) Real) :
    (precond2ApplyPlan P R).1 = precond2Apply P R ∧
    precond2ApplyTraceCost n r (precond2ApplyPlan P R).2 = precond2ApplyCost n r ∧
    precond2Apply P R
      = P.K⁻¹ * R * (gramMatrix P + P.lam • (1 : Matrix (Fin r) (Fin r) Real))⁻¹ := by
  exact precond2ApplyPlan_bridge (P := P) hLam hKpos R

end
end Q10
end AutoProof
