import autoproof.Q10.TraceAndRates.TraceModels

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Standard CG/PCG linear-rate factor from condition number `κ`:
`ρ(κ) = (sqrt κ - 1) / (sqrt κ + 1)`. -/
def pcgRate (kappa : Real) : Real :=
  (Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)

theorem pcgRate_nonneg {kappa : Real} (hKappa : 1 < kappa) :
    0 ≤ pcgRate kappa := by
  unfold pcgRate
  have hsqrt_gt1 : 1 < Real.sqrt kappa := by
    have hsqrt : Real.sqrt (1 : Real) < Real.sqrt kappa := by
      exact (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ 1 by norm_num)).2 hKappa
    simpa using hsqrt
  have hnum_nonneg : 0 ≤ Real.sqrt kappa - 1 := by linarith
  have hden_nonneg : 0 ≤ Real.sqrt kappa + 1 := by linarith
  exact div_nonneg hnum_nonneg hden_nonneg

theorem pcgRate_lt_one {kappa : Real} (hKappa : 1 < kappa) :
    pcgRate kappa < 1 := by
  unfold pcgRate
  have hsqrt_gt1 : 1 < Real.sqrt kappa := by
    have hsqrt : Real.sqrt (1 : Real) < Real.sqrt kappa := by
      exact (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ 1 by norm_num)).2 hKappa
    simpa using hsqrt
  have hden_pos : 0 < Real.sqrt kappa + 1 := by linarith
  have hnum_lt_den : Real.sqrt kappa - 1 < Real.sqrt kappa + 1 := by linarith
  exact (div_lt_one hden_pos).2 hnum_lt_den

/-- Monotonicity of the standard CG/PCG rate factor on `(1,∞)`:
larger condition number gives larger linear-rate factor. -/
theorem pcgRate_mono
    {kappa1 kappa2 : Real}
    (hKappa1 : 1 < kappa1) (hKappa2 : 1 < kappa2)
    (hOrder : kappa1 ≤ kappa2) :
    pcgRate kappa1 ≤ pcgRate kappa2 := by
  unfold pcgRate
  have hsqrt : Real.sqrt kappa1 ≤ Real.sqrt kappa2 := Real.sqrt_le_sqrt hOrder
  have hsqrt1_gt1 : 1 < Real.sqrt kappa1 := by
    have hsqrt : Real.sqrt (1 : Real) < Real.sqrt kappa1 := by
      exact (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ 1 by norm_num)).2 hKappa1
    simpa using hsqrt
  have hsqrt2_gt1 : 1 < Real.sqrt kappa2 := by
    have hsqrt : Real.sqrt (1 : Real) < Real.sqrt kappa2 := by
      exact (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ 1 by norm_num)).2 hKappa2
    simpa using hsqrt
  have hden1 : 0 < Real.sqrt kappa1 + 1 := by linarith
  have hden2 : 0 < Real.sqrt kappa2 + 1 := by linarith
  have hcross :
      (Real.sqrt kappa1 - 1) * (Real.sqrt kappa2 + 1)
        ≤ (Real.sqrt kappa2 - 1) * (Real.sqrt kappa1 + 1) := by
    nlinarith
  have hstep :
      (Real.sqrt kappa1 - 1) / (Real.sqrt kappa1 + 1) * (Real.sqrt kappa2 + 1)
        ≤ (Real.sqrt kappa2 - 1) := by
    have hdiv : (Real.sqrt kappa1 - 1) * (Real.sqrt kappa2 + 1) / (Real.sqrt kappa1 + 1)
        ≤ (Real.sqrt kappa2 - 1) := (div_le_iff₀ hden1).2 hcross
    have hmuldiv :
        (Real.sqrt kappa1 - 1) / (Real.sqrt kappa1 + 1) * (Real.sqrt kappa2 + 1)
          = (Real.sqrt kappa1 - 1) * (Real.sqrt kappa2 + 1) / (Real.sqrt kappa1 + 1) := by
      ring
    simpa [hmuldiv] using hdiv
  exact (le_div_iff₀ hden2).2 hstep

theorem pcgRate_strict_mono
    {kappa1 kappa2 : Real}
    (hKappa1 : 1 < kappa1) (hKappa2 : 1 < kappa2)
    (hOrder : kappa1 < kappa2) :
    pcgRate kappa1 < pcgRate kappa2 := by
  unfold pcgRate
  have hsqrt : Real.sqrt kappa1 < Real.sqrt kappa2 :=
    (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ kappa1 by linarith)).2 hOrder
  have hden1 : 0 < Real.sqrt kappa1 + 1 := by
    have hsqrt1_gt1 : 1 < Real.sqrt kappa1 := by
      have hsqrt1 : Real.sqrt (1 : Real) < Real.sqrt kappa1 := by
        exact (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ 1 by norm_num)).2 hKappa1
      simpa using hsqrt1
    linarith
  have hden2 : 0 < Real.sqrt kappa2 + 1 := by
    have hsqrt2_gt1 : 1 < Real.sqrt kappa2 := by
      have hsqrt2 : Real.sqrt (1 : Real) < Real.sqrt kappa2 := by
        exact (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ 1 by norm_num)).2 hKappa2
      simpa using hsqrt2
    linarith
  rw [div_lt_div_iff₀ hden1 hden2]
  nlinarith

/-- Residual norm sequence for a fixed PCG run setup. -/
def pcgResidualNorm (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat) : Real :=
  ‖(pcgRun P Minv x0 k).r.vec‖

theorem pcgResidualNorm_nonneg (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real) (k : Nat) :
    0 ≤ pcgResidualNorm P Minv x0 k := by
  simp [pcgResidualNorm]

/-- Stepwise contraction implies a global geometric bound for `pcgResidualNorm`. -/
theorem pcgResidualNorm_geometric_of_stepwise
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {rho : Real}
    (hRhoNonneg : 0 ≤ rho)
    (hRecurrence :
      ∀ k : Nat, pcgResidualNorm P Minv x0 (k + 1)
        ≤ rho * pcgResidualNorm P Minv x0 k) :
    ∀ k : Nat,
      pcgResidualNorm P Minv x0 k
        ≤ rho ^ k * pcgResidualNorm P Minv x0 0 := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        pcgResidualNorm P Minv x0 (k + 1)
            ≤ rho * pcgResidualNorm P Minv x0 k := hRecurrence k
        _ ≤ rho * (rho ^ k * pcgResidualNorm P Minv x0 0) := by
              exact mul_le_mul_of_nonneg_left ih hRhoNonneg
        _ = rho ^ (k + 1) * pcgResidualNorm P Minv x0 0 := by
              simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Algorithm-recursive rate closure:
if each PCG step contracts with factor `pcgRate κ` and the initial residual
is bounded by `2*err0`, then the standard global `2*(pcgRate κ)^k*err0` bound follows. -/
theorem pcgResidualNorm_standard_rate_of_stepwise
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {kappa err0 : Real}
    (hKappa : 1 < kappa)
    (hInit : pcgResidualNorm P Minv x0 0 ≤ 2 * err0)
    (hRecurrence :
      ∀ k : Nat, pcgResidualNorm P Minv x0 (k + 1)
        ≤ pcgRate kappa * pcgResidualNorm P Minv x0 k) :
    ∀ k : Nat,
      pcgResidualNorm P Minv x0 k
        ≤ 2 * (pcgRate kappa) ^ k * err0 := by
  intro k
  have hGeom := pcgResidualNorm_geometric_of_stepwise
    (P := P) (Minv := Minv) (x0 := x0)
    (hRhoNonneg := pcgRate_nonneg hKappa) (hRecurrence := hRecurrence) k
  have hPowNonneg : 0 ≤ (pcgRate kappa) ^ k :=
    pow_nonneg (pcgRate_nonneg hKappa) k
  have hInitScaled :
      (pcgRate kappa) ^ k * pcgResidualNorm P Minv x0 0
        ≤ (pcgRate kappa) ^ k * (2 * err0) := by
    exact mul_le_mul_of_nonneg_left hInit hPowNonneg
  calc
    pcgResidualNorm P Minv x0 k
        ≤ (pcgRate kappa) ^ k * pcgResidualNorm P Minv x0 0 := hGeom
    _ ≤ (pcgRate kappa) ^ k * (2 * err0) := hInitScaled
    _ = 2 * (pcgRate kappa) ^ k * err0 := by ring

/-- Generic closure of the standard CG/PCG rate model:
if `err k ≤ 2 * ρ^k * err0` with `ρ = pcgRate κ`, then some finite iterate reaches any `eps > 0`. -/
theorem exists_iter_le_tol_of_standard_rate_bound
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa) (hErr0 : 0 < err0) (hEps : 0 < eps)
    (err : Nat → Real)
    (hBound : ∀ k : Nat, err k ≤ 2 * (pcgRate kappa) ^ k * err0) :
    ∃ k : Nat, err k ≤ eps := by
  have hdelta : 0 < eps / (2 * err0) := by
    have h2e0 : 0 < 2 * err0 := by nlinarith
    exact div_pos hEps h2e0
  have hRateLtOne : pcgRate kappa < 1 := pcgRate_lt_one hKappa
  rcases exists_pow_lt_of_lt_one hdelta hRateLtOne with ⟨k, hkPow⟩
  have h2e0Pos : 0 < 2 * err0 := by nlinarith
  have hScaled :
      (2 * err0) * (pcgRate kappa) ^ k < (2 * err0) * (eps / (2 * err0)) :=
    mul_lt_mul_of_pos_left hkPow h2e0Pos
  have hCancel : (2 * err0) * (eps / (2 * err0)) = eps := by
    field_simp [ne_of_gt h2e0Pos]
  have hTol : 2 * (pcgRate kappa) ^ k * err0 ≤ eps := by
    have hLt : 2 * (pcgRate kappa) ^ k * err0 < eps := by
      calc
        2 * (pcgRate kappa) ^ k * err0 = (2 * err0) * (pcgRate kappa) ^ k := by ring
        _ < (2 * err0) * (eps / (2 * err0)) := hScaled
        _ = eps := hCancel
    exact le_of_lt hLt
  exact ⟨k, le_trans (hBound k) hTol⟩

theorem exists_iter_model_rate_le_tol
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa) (hErr0 : 0 < err0) (hEps : 0 < eps) :
    ∃ k : Nat, 2 * (pcgRate kappa) ^ k * err0 ≤ eps := by
  simpa using exists_iter_le_tol_of_standard_rate_bound
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
    (err := fun k : Nat => 2 * (pcgRate kappa) ^ k * err0)
    (hBound := fun _ => le_rfl)

/-- Human-readable sqrt-form of the model-rate existence bound:
`∃ k, 2 * ((sqrt κ - 1)/(sqrt κ + 1))^k * err0 ≤ eps`. -/
theorem exists_iter_model_rate_le_tol_sqrt_form
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa) (hErr0 : 0 < err0) (hEps : 0 < eps) :
    ∃ k : Nat,
      2 * (((Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)) ^ k) * err0 ≤ eps := by
  simpa [pcgRate] using exists_iter_model_rate_le_tol
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)

/-- Minimal model iteration index reaching tolerance under the standard
`2 * ρ^k * err0` rate envelope. -/
noncomputable def modelTolIter
    (kappa err0 eps : Real)
    (hKappa : 1 < kappa) (hErr0 : 0 < err0) (hEps : 0 < eps) : Nat :=
  Nat.find (exists_iter_model_rate_le_tol (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps))

theorem modelTolIter_spec
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa) (hErr0 : 0 < err0) (hEps : 0 < eps) :
    2 * (pcgRate kappa) ^ (modelTolIter kappa err0 eps hKappa hErr0 hEps) * err0 ≤ eps := by
  unfold modelTolIter
  exact Nat.find_spec (exists_iter_model_rate_le_tol
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps))

/-- Human-readable sqrt-form at the canonical model-tolerance index. -/
theorem modelTolIter_spec_sqrt_form
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa) (hErr0 : 0 < err0) (hEps : 0 < eps) :
    2 * (((Real.sqrt kappa - 1) / (Real.sqrt kappa + 1))
      ^ (modelTolIter kappa err0 eps hKappa hErr0 hEps)) * err0 ≤ eps := by
  simpa [pcgRate] using modelTolIter_spec
    (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)

/-- Explicit log/ceil iteration bound for the model-rate envelope:
if `k ≥ ceil(log(eps/(2*err0)) / log(rho))` with `rho = pcgRate kappa ∈ (0,1)`,
then `2 * rho^k * err0 ≤ eps`. -/
theorem model_rate_le_tol_of_ge_ceil_log_ratio
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa) (hErr0 : 0 < err0) (hEps : 0 < eps)
    {k : Nat}
    (hk :
      (⌈Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)⌉₊ : Nat) ≤ k) :
    2 * (pcgRate kappa) ^ k * err0 ≤ eps := by
  have hRateLtOne : pcgRate kappa < 1 := pcgRate_lt_one hKappa
  have hRatePos : 0 < pcgRate kappa := by
    unfold pcgRate
    have hsqrt_gt1 : 1 < Real.sqrt kappa := by
      have hsqrt : Real.sqrt (1 : Real) < Real.sqrt kappa := by
        exact (Real.sqrt_lt_sqrt_iff (show (0 : Real) ≤ 1 by norm_num)).2 hKappa
      simpa using hsqrt
    have hnum_pos : 0 < Real.sqrt kappa - 1 := by linarith
    have hden_pos : 0 < Real.sqrt kappa + 1 := by linarith
    exact div_pos hnum_pos hden_pos
  have hRateNeZero : pcgRate kappa ≠ 0 := ne_of_gt hRatePos
  have hRateNeOne : pcgRate kappa ≠ 1 := ne_of_lt hRateLtOne
  have hRateNeNegOne : pcgRate kappa ≠ -1 := by linarith
  have hLogRateNeZero : Real.log (pcgRate kappa) ≠ 0 := by
    exact (Real.log_ne_zero).2 ⟨hRateNeZero, hRateNeOne, hRateNeNegOne⟩
  have hDeltaPos : 0 < eps / (2 * err0) := by
    have h2e0Pos : 0 < 2 * err0 := by linarith
    exact div_pos hEps h2e0Pos
  have hArgLeK :
      Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa) ≤ (k : Real) := by
    have hLeCeil :
        Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)
          ≤ (⌈Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)⌉₊ : Nat) :=
      Nat.le_ceil _
    have hCeilLeK : ((⌈Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)⌉₊ : Nat) : Real)
        ≤ (k : Real) := by
      exact_mod_cast hk
    exact le_trans hLeCeil hCeilLeK
  have hPowLe :
      (pcgRate kappa) ^ (k : Real)
        ≤ (pcgRate kappa) ^ (Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)) := by
    exact (Real.antitone_rpow_of_base_le_one hRatePos (le_of_lt hRateLtOne)) hArgLeK
  have hPowEq :
      (pcgRate kappa) ^ (Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa))
        = eps / (2 * err0) := by
    calc
      (pcgRate kappa) ^ (Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa))
          = Real.exp
              (Real.log (pcgRate kappa)
                * (Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa))) := by
              rw [Real.rpow_def_of_pos hRatePos]
      _ = Real.exp (Real.log (eps / (2 * err0))) := by
            field_simp [hLogRateNeZero]
      _ = eps / (2 * err0) := by
            exact Real.exp_log hDeltaPos
  have hPowNatLe :
      (pcgRate kappa) ^ k ≤ eps / (2 * err0) := by
    calc
      (pcgRate kappa) ^ k = (pcgRate kappa) ^ (k : Real) := by
        symm
        exact Real.rpow_natCast (pcgRate kappa) k
      _ ≤ (pcgRate kappa) ^ (Real.log (eps / (2 * err0)) / Real.log (pcgRate kappa)) := hPowLe
      _ = eps / (2 * err0) := hPowEq
  have h2e0Pos : 0 < 2 * err0 := by linarith
  have hScaled :
      ((pcgRate kappa) ^ k) * (2 * err0) ≤ (eps / (2 * err0)) * (2 * err0) := by
    exact mul_le_mul_of_nonneg_right hPowNatLe (le_of_lt h2e0Pos)
  calc
    2 * (pcgRate kappa) ^ k * err0 = ((pcgRate kappa) ^ k) * (2 * err0) := by ring
    _ ≤ (eps / (2 * err0)) * (2 * err0) := hScaled
    _ = eps := by
          field_simp [ne_of_gt h2e0Pos]

/-- The model tolerance index is a valid PCG tolerance index under stepwise contraction. -/
theorem pcgResidualNorm_le_tol_at_modelTolIter_of_stepwise
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0) (hEps : 0 < eps)
    (hInit : pcgResidualNorm P Minv x0 0 ≤ 2 * err0)
    (hRecurrence :
      ∀ k : Nat, pcgResidualNorm P Minv x0 (k + 1)
        ≤ pcgRate kappa * pcgResidualNorm P Minv x0 k) :
    pcgResidualNorm P Minv x0 (modelTolIter kappa err0 eps hKappa hErr0 hEps) ≤ eps := by
  have hBound : ∀ k : Nat,
      pcgResidualNorm P Minv x0 k ≤ 2 * (pcgRate kappa) ^ k * err0 :=
    pcgResidualNorm_standard_rate_of_stepwise
      (P := P) (Minv := Minv) (x0 := x0)
      (hKappa := hKappa) (hInit := hInit) (hRecurrence := hRecurrence)
  have hModel := modelTolIter_spec (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
  exact le_trans (hBound _) hModel

/-- Polynomial-envelope residual bound for unpreconditioned CG (`Minv = id`):
if each admissible degree-`k` polynomial action is bounded by
`2 * rho^k * err0`, then the concrete `k`-step residual has the same bound. -/
theorem pcgResidualNorm_le_of_poly_rate_envelope_id
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {rho err0 : Real}
    (hPolyEnvelope :
      ∀ k : Nat, ∀ p : Polynomial Real, p.eval 0 = 1 → p.natDegree ≤ k →
        ‖(polyApplyLin (applyALin P) p (pcgR0 P x0)).vec‖ ≤ 2 * rho ^ k * err0) :
    ∀ k : Nat, ‖(pcgRun P idPrecond x0 k).r.vec‖ ≤ 2 * rho ^ k * err0 := by
  intro k
  rcases pcgRun_id_residual_search_poly_evalZero_deg (P := P) (x0 := x0) k with
    ⟨pr, pp, hpr, hpp, hpr0, hdegR, hdegP⟩
  calc
    ‖(pcgRun P idPrecond x0 k).r.vec‖
        = ‖(polyApplyLin (applyALin P) pr (pcgR0 P x0)).vec‖ := by
            simpa [hpr]
    _ ≤ 2 * rho ^ k * err0 := hPolyEnvelope k pr hpr0 hdegR

/-- Polynomial-envelope variant of `pcgResidualNorm_le_tol_at_modelTolIter_of_stepwise`
for unpreconditioned CG (`Minv = id`): no stepwise-contraction hypothesis is needed,
only the degree-`k` polynomial majorant family. -/
theorem pcgResidualNorm_le_tol_at_modelTolIter_of_poly_rate_envelope_id
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {kappa err0 eps : Real}
    (hKappa : 1 < kappa)
    (hErr0 : 0 < err0) (hEps : 0 < eps)
    (hPolyBound :
      ∀ k : Nat, ∀ p : Polynomial Real, p.eval 0 = 1 → p.natDegree ≤ k →
        ‖(polyApplyLin (applyALin P) p (pcgR0 P x0)).vec‖ ≤
          2 * (pcgRate kappa) ^ k * err0) :
    pcgResidualNorm P idPrecond x0
      (modelTolIter kappa err0 eps hKappa hErr0 hEps) ≤ eps := by
  have hBoundRaw : ∀ k : Nat,
      ‖(pcgRun P idPrecond x0 k).r.vec‖ ≤ 2 * (pcgRate kappa) ^ k * err0 :=
    pcgResidualNorm_le_of_poly_rate_envelope_id
      (P := P) (x0 := x0) (rho := pcgRate kappa) (err0 := err0) (by
        intro k p hp0 hdeg
        simpa using hPolyBound k p hp0 hdeg)
  have hBound : ∀ k : Nat,
      pcgResidualNorm P idPrecond x0 k ≤ 2 * (pcgRate kappa) ^ k * err0 := by
    intro k
    simpa [pcgResidualNorm] using hBoundRaw k
  have hModel := modelTolIter_spec (hKappa := hKappa) (hErr0 := hErr0) (hEps := hEps)
  exact le_trans (hBound _) hModel

/-- Preconditioned polynomial-recursion envelope to concrete residual-rate bound:
if the canonical preconditioned residual polynomial action is bounded by
`2 * (pcgRate κ)^k * err0z`, and `MinvInv` is a stable left-inverse of `Minv`,
then the concrete residual norm inherits the same rate up to factor `c`. -/
theorem pcgResidualNorm_le_of_precond_polyRec_envelope
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (MinvInv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {kappa err0z c : Real}
    (hMinv : ∀ X : Matrix (Fin n) (Fin r) Real, Minv X = MinvLin X)
    (hLeftInv : ∀ X : Matrix (Fin n) (Fin r) Real, MinvInv (Minv X) = X)
    (hc : 0 ≤ c)
    (hInvBound : ∀ X : Matrix (Fin n) (Fin r) Real,
      ‖(MinvInv X).vec‖ ≤ c * ‖X.vec‖)
    (hPolyBound :
      ∀ k : Nat,
        ‖(polyApplyLin (precondApplyALin P MinvLin)
            (pcgPrecondResidualPolyRec P Minv x0 k) (Minv (pcgR0 P x0))).vec‖
          ≤ 2 * (pcgRate kappa) ^ k * err0z) :
    ∀ k : Nat,
      pcgResidualNorm P Minv x0 k
        ≤ c * (2 * (pcgRate kappa) ^ k * err0z) := by
  intro k
  have hCore :
      ‖(pcgRun P Minv x0 k).r.vec‖
        ≤ c * ‖(polyApplyLin (precondApplyALin P MinvLin)
            (pcgPrecondResidualPolyRec P Minv x0 k) (Minv (pcgR0 P x0))).vec‖ :=
    pcgRun_precond_residual_norm_le_leftInverse_polyRec
      (P := P) (Minv := Minv) (MinvLin := MinvLin) (MinvInv := MinvInv)
      (x0 := x0) (hMinv := hMinv) (hLeftInv := hLeftInv) (hInvBound := hInvBound) k
  have hLift :
      c * ‖(polyApplyLin (precondApplyALin P MinvLin)
          (pcgPrecondResidualPolyRec P Minv x0 k) (Minv (pcgR0 P x0))).vec‖
        ≤ c * (2 * (pcgRate kappa) ^ k * err0z) := by
    exact mul_le_mul_of_nonneg_left (hPolyBound k) hc
  exact le_trans hCore hLift

/-- Model-tolerance version of `pcgResidualNorm_le_of_precond_polyRec_envelope`:
at the model index for the `z`-envelope, residual is bounded by `c * eps`. -/
theorem pcgResidualNorm_le_cmul_tol_at_modelTolIter_of_precond_polyRec_envelope
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (MinvLin : Matrix (Fin n) (Fin r) Real →ₗ[Real] Matrix (Fin n) (Fin r) Real)
    (MinvInv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {kappa err0z eps c : Real}
    (hMinv : ∀ X : Matrix (Fin n) (Fin r) Real, Minv X = MinvLin X)
    (hLeftInv : ∀ X : Matrix (Fin n) (Fin r) Real, MinvInv (Minv X) = X)
    (hc : 0 ≤ c)
    (hKappa : 1 < kappa)
    (hErr0z : 0 < err0z)
    (hEps : 0 < eps)
    (hInvBound : ∀ X : Matrix (Fin n) (Fin r) Real,
      ‖(MinvInv X).vec‖ ≤ c * ‖X.vec‖)
    (hPolyBound :
      ∀ k : Nat,
        ‖(polyApplyLin (precondApplyALin P MinvLin)
            (pcgPrecondResidualPolyRec P Minv x0 k) (Minv (pcgR0 P x0))).vec‖
          ≤ 2 * (pcgRate kappa) ^ k * err0z) :
    pcgResidualNorm P Minv x0 (modelTolIter kappa err0z eps hKappa hErr0z hEps) ≤ c * eps := by
  have hRate :=
    pcgResidualNorm_le_of_precond_polyRec_envelope
      (P := P) (Minv := Minv) (MinvLin := MinvLin) (MinvInv := MinvInv)
      (x0 := x0) (kappa := kappa) (err0z := err0z) (c := c)
      (hMinv := hMinv) (hLeftInv := hLeftInv) (hc := hc)
      (hInvBound := hInvBound) (hPolyBound := hPolyBound)
  have hModel :
      2 * (pcgRate kappa) ^ (modelTolIter kappa err0z eps hKappa hErr0z hEps) * err0z ≤ eps :=
    modelTolIter_spec (hKappa := hKappa) (hErr0 := hErr0z) (hEps := hEps)
  have hScale :
      c * (2 * (pcgRate kappa) ^ (modelTolIter kappa err0z eps hKappa hErr0z hEps) * err0z)
        ≤ c * eps := by
    exact mul_le_mul_of_nonneg_left hModel hc
  exact le_trans (hRate _) hScale

theorem modelTolIter_le_of_rate_le
    {kappa1 kappa2 err0 eps : Real}
    (hKappa1 : 1 < kappa1) (hKappa2 : 1 < kappa2)
    (hErr0 : 0 < err0) (hEps : 0 < eps)
    (hRate : pcgRate kappa2 ≤ pcgRate kappa1) :
    modelTolIter kappa2 err0 eps hKappa2 hErr0 hEps
      ≤ modelTolIter kappa1 err0 eps hKappa1 hErr0 hEps := by
  let k1 := modelTolIter kappa1 err0 eps hKappa1 hErr0 hEps
  have hk1 : 2 * (pcgRate kappa1) ^ k1 * err0 ≤ eps := by
    simpa [k1] using modelTolIter_spec (hKappa := hKappa1) (hErr0 := hErr0) (hEps := hEps)
  have hPow : (pcgRate kappa2) ^ k1 ≤ (pcgRate kappa1) ^ k1 := by
    exact pow_le_pow_left₀ (pcgRate_nonneg hKappa2) hRate k1
  have hScale :
      2 * (pcgRate kappa2) ^ k1 * err0 ≤ 2 * (pcgRate kappa1) ^ k1 * err0 := by
    nlinarith [hPow, hErr0]
  have hk1' : 2 * (pcgRate kappa2) ^ k1 * err0 ≤ eps := le_trans hScale hk1
  exact Nat.find_min' (exists_iter_model_rate_le_tol
    (hKappa := hKappa2) (hErr0 := hErr0) (hEps := hEps)) hk1'

theorem modelTolIter_le_of_kappa_le
    {kappa1 kappa2 err0 eps : Real}
    (hKappa1 : 1 < kappa1) (hKappa2 : 1 < kappa2)
    (hErr0 : 0 < err0) (hEps : 0 < eps)
    (hKappaOrder : kappa2 ≤ kappa1) :
    modelTolIter kappa2 err0 eps hKappa2 hErr0 hEps
      ≤ modelTolIter kappa1 err0 eps hKappa1 hErr0 hEps := by
  exact modelTolIter_le_of_rate_le
    (hKappa1 := hKappa1) (hKappa2 := hKappa2) (hErr0 := hErr0) (hEps := hEps)
    (hRate := pcgRate_mono (hKappa1 := hKappa2) (hKappa2 := hKappa1) hKappaOrder)


end
end Q10
end AutoProof
