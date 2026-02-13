import autoproof.Q10.Core.KrylovAlgorithm.DefsAndPoly

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

variable {n M r q : Nat}

/-- Algorithm-to-polynomial bridge for unpreconditioned CG:
if all admissible degree-`k` residual polynomials satisfy a norm envelope `≤ c`,
then the actual `k`-step residual norm also satisfies `≤ c`. -/
theorem pcgResidualNorm_le_of_poly_envelope_id
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (k : Nat) {c : Real}
    (hPolyBound :
      ∀ p : Polynomial Real, p.eval 0 = 1 → p.natDegree ≤ k →
        ‖(polyApplyLin (applyALin P) p (pcgR0 P x0)).vec‖ ≤ c) :
    ‖(pcgRun P idPrecond x0 k).r.vec‖ ≤ c := by
  rcases pcgRun_id_residual_search_poly_evalZero_deg (P := P) (x0 := x0) k with
    ⟨pr, pp, hpr, hpp, hpr0, hdegR, hdegP⟩
  have hprBound : ‖(polyApplyLin (applyALin P) pr (pcgR0 P x0)).vec‖ ≤ c :=
    hPolyBound pr hpr0 hdegR
  simpa [hpr] using hprBound

/-- Rate-envelope specialization of `pcgResidualNorm_le_of_poly_envelope_id`:
any explicit polynomial majorant transfers directly to the concrete `pcgRun` residuals. -/
theorem pcgResidualNorm_le_of_poly_rate_envelope_id
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    {rho err0 : Real}
    (hPolyBound :
      ∀ k : Nat, ∀ p : Polynomial Real, p.eval 0 = 1 → p.natDegree ≤ k →
        ‖(polyApplyLin (applyALin P) p (pcgR0 P x0)).vec‖ ≤
          2 * rho ^ k * err0) :
    ∀ k : Nat, ‖(pcgRun P idPrecond x0 k).r.vec‖ ≤ 2 * rho ^ k * err0 := by
  intro k
  exact pcgResidualNorm_le_of_poly_envelope_id
    (P := P) (x0 := x0) (k := k)
    (hPolyBound := hPolyBound k)

/-- For identity preconditioning, the auxiliary vector coincides with residual
at every iterate: `z_k = r_k`. -/
theorem pcgRun_id_z_eq_r
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real) :
    ∀ k : Nat, (pcgRun P idPrecond x0 k).z = (pcgRun P idPrecond x0 k).r := by
  intro k
  induction k with
  | zero =>
      simp [pcgRun, pcgInit, idPrecond]
  | succ k ih =>
      simpa [pcgRun, pcgStep, pcgZNext, idPrecond, ih]

/-- If `z = r` (identity preconditioning) and `⟪r,p⟫ = ⟪r,r⟫`,
then the PCG step size can be written in the usual CG form
`α = ⟪r,p⟫ / ⟪p,Ap⟫`. -/
theorem pcgAlpha_eq_residual_search_ratio_of_z_eq_r
    (P : Problem n M r q)
    (st : PCGState n r)
    (hz : st.z = st.r)
    (hRp : frobInner st.r st.p = frobInner st.r st.r) :
    pcgAlpha P st = frobInner st.r st.p / frobInner st.p (pcgAp P st) := by
  unfold pcgAlpha
  rw [hz]
  rw [← hRp]

/-- Error matrix against a reference solution `xStar`. -/
def pcgError {n r : Nat}
    (xStar : Matrix (Fin n) (Fin r) Real) (st : PCGState n r) :
    Matrix (Fin n) (Fin r) Real :=
  xStar - st.x

/-- If `xStar` solves the linear system and `st` satisfies the residual invariant,
then `r = A * error`. -/
theorem pcgResidual_eq_applyA_error
    (P : Problem n M r q)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real)
    (hSol : applyA P xStar = rhsMat P)
    (hRes : st.r = rhsMat P - applyA P st.x) :
    st.r = applyA P (pcgError xStar st) := by
  unfold pcgError
  calc
    st.r = rhsMat P - applyA P st.x := hRes
    _ = applyA P xStar - applyA P st.x := by rw [← hSol]
    _ = applyA P (xStar - st.x) := by
          symm
          simpa using (applyA_sub_smul (P := P) xStar st.x (1 : Real))

/-- Convert `⟪error, Ap⟫` into `⟪r,p⟫` once `r = A*error`. -/
theorem frobInner_error_ap_eq_residual_search
    (P : Problem n M r q)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real)
    (hErr : st.r = applyA P (pcgError xStar st)) :
    frobInner (pcgError xStar st) (pcgAp P st) = frobInner st.r st.p := by
  calc
    frobInner (pcgError xStar st) (pcgAp P st)
        = frobInner st.p (applyA P (pcgError xStar st)) := by
            simpa [pcgAp] using
              (frobInner_applyA_comm (P := P) (X := pcgError xStar st) (Y := st.p))
    _ = frobInner st.p st.r := by rw [← hErr]
    _ = frobInner st.r st.p := by
          unfold frobInner
          simpa using dotProduct_comm st.p.vec st.r.vec

/-- Identity-preconditioned `alpha` expressed as
`⟪error, Ap⟫ / ⟪p,Ap⟫` once `xStar` is fixed. -/
theorem pcgAlpha_eq_error_search_ratio_of_id
    (P : Problem n M r q)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real)
    (hz : st.z = st.r)
    (hRp : frobInner st.r st.p = frobInner st.r st.r)
    (hErr : st.r = applyA P (pcgError xStar st)) :
    pcgAlpha P st
      = frobInner (pcgError xStar st) (pcgAp P st) / frobInner st.p (pcgAp P st) := by
  have hNum1 : frobInner st.r st.z = frobInner st.r st.p := by
    rw [hz, hRp]
  have hNum2 : frobInner st.r st.p = frobInner (pcgError xStar st) (pcgAp P st) := by
    symm
    exact frobInner_error_ap_eq_residual_search (P := P) (st := st) (xStar := xStar) hErr
  unfold pcgAlpha
  rw [hNum1, hNum2]

/-- One-step update of the error variable. -/
theorem pcgError_step
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real) :
    pcgError xStar (pcgStep P Minv st)
      = pcgError xStar st - pcgAlpha P st • st.p := by
  unfold pcgError pcgStep pcgXNext
  simp [sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm]

/-- Along the current search line, the CG `alpha` minimizes the quadratic
`⟪e - t p, A(e - t p)⟫` once `r = A e` and `⟪r,p⟫ = ⟪r,r⟫`. -/
theorem pcgAlpha_minimizes_error_energy_along_search_of_id
    (P : Problem n M r q)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real)
    (hSPD : operatorSPD P)
    (hz : st.z = st.r)
    (hRp : frobInner st.r st.p = frobInner st.r st.r)
    (hRes : st.r = rhsMat P - applyA P st.x)
    (hSol : applyA P xStar = rhsMat P)
    (hp : st.p ≠ 0)
    (a : Real) :
    frobInner (pcgError xStar st - pcgAlpha P st • st.p)
      (applyA P (pcgError xStar st - pcgAlpha P st • st.p))
      ≤
    frobInner (pcgError xStar st - a • st.p)
      (applyA P (pcgError xStar st - a • st.p)) := by
  let e : Matrix (Fin n) (Fin r) Real := pcgError xStar st
  let d : Real := frobInner st.p (pcgAp P st)
  let n0 : Real := frobInner e (pcgAp P st)
  have hErr : st.r = applyA P e := by
    simpa [e] using
      pcgResidual_eq_applyA_error (P := P) (st := st) (xStar := xStar) hSol hRes
  have hDenPos : 0 < d := by
    simpa [d] using
      pcgAlpha_den_pos_of_operatorSPD (P := P) (st := st) hSPD hp
  have hAlpha : pcgAlpha P st = n0 / d := by
    unfold d n0
    simpa [e] using
      pcgAlpha_eq_error_search_ratio_of_id
        (P := P) (st := st) (xStar := xStar) hz hRp hErr
  have hLeft :
      frobInner (e - pcgAlpha P st • st.p) (applyA P (e - pcgAlpha P st • st.p))
        = frobInner e (applyA P e) - 2 * (n0 / d) * n0 + (n0 / d) ^ 2 * d := by
    calc
      frobInner (e - pcgAlpha P st • st.p) (applyA P (e - pcgAlpha P st • st.p))
          = frobInner e (applyA P e)
              - 2 * pcgAlpha P st * frobInner e (applyA P st.p)
              + (pcgAlpha P st) ^ 2 * frobInner st.p (applyA P st.p) := by
                simpa using energy_along_search_expand_symm (P := P) e st.p (pcgAlpha P st)
      _ = frobInner e (applyA P e) - 2 * pcgAlpha P st * n0 + (pcgAlpha P st) ^ 2 * d := by
            simp [n0, d, pcgAp]
      _ = frobInner e (applyA P e) - 2 * (n0 / d) * n0 + (n0 / d) ^ 2 * d := by
            rw [hAlpha]
  have hRight :
      frobInner (e - a • st.p) (applyA P (e - a • st.p))
        = frobInner e (applyA P e) - 2 * a * n0 + a ^ 2 * d := by
    calc
      frobInner (e - a • st.p) (applyA P (e - a • st.p))
          = frobInner e (applyA P e)
              - 2 * a * frobInner e (applyA P st.p)
              + a ^ 2 * frobInner st.p (applyA P st.p) := by
                simpa using energy_along_search_expand_symm (P := P) e st.p a
      _ = frobInner e (applyA P e) - 2 * a * n0 + a ^ 2 * d := by
            simp [n0, d, pcgAp]
  have hQuad :
      (n0 / d) ^ 2 * d - 2 * n0 * (n0 / d)
        ≤ a ^ 2 * d - 2 * n0 * a :=
    quadratic_minimizer_linear_term (d := d) (n := n0) (a := a) hDenPos
  have hQuad' :
      -2 * (n0 / d) * n0 + (n0 / d) ^ 2 * d
        ≤ -2 * a * n0 + a ^ 2 * d := by
    nlinarith [hQuad]
  have hMain :
      frobInner e (applyA P e) - 2 * (n0 / d) * n0 + (n0 / d) ^ 2 * d
        ≤ frobInner e (applyA P e) - 2 * a * n0 + a ^ 2 * d := by
    nlinarith [hQuad']
  calc
    frobInner (pcgError xStar st - pcgAlpha P st • st.p)
        (applyA P (pcgError xStar st - pcgAlpha P st • st.p))
        = frobInner e (applyA P e) - 2 * (n0 / d) * n0 + (n0 / d) ^ 2 * d := by
            simpa [e] using hLeft
    _ ≤ frobInner e (applyA P e) - 2 * a * n0 + a ^ 2 * d := hMain
    _ = frobInner (pcgError xStar st - a • st.p)
          (applyA P (pcgError xStar st - a • st.p)) := by
          simpa [e] using hRight.symm

/-- Numeric witness that CG's first-step scalar
`α = (r·r)/(r·Ar)` need not be the Euclidean residual line-search minimizer
`a* = (r·Ar)/(Ar·Ar)`. This blocks a direct proof of residual-minimax dominance
from the raw `pcgRun` recursion. -/
theorem cg_alpha_not_euclidean_residual_line_search_minimizer_witness :
    let alpha : Real := (5 : Real) / 20
    let aLS : Real := (20 : Real) / 85
    ((1 - aLS * 6) ^ 2 + (2 - aLS * 7) ^ 2)
      < ((1 - alpha * 6) ^ 2 + (2 - alpha * 7) ^ 2) := by
  norm_num

/-- If `z = r` and `r = 0`, then `α = 0` in the PCG update formula. -/
theorem pcgAlpha_eq_zero_of_z_eq_r_of_r_eq_zero
    (P : Problem n M r q)
    (st : PCGState n r)
    (hz : st.z = st.r)
    (hr0 : st.r = 0) :
    pcgAlpha P st = 0 := by
  have hnum0 : frobInner st.r st.z = 0 := by
    rw [hz, hr0]
    simp [frobInner_zero_left]
  unfold pcgAlpha
  rw [hnum0, zero_div]

/-- Expand `⟪r - a Ap, p⟫` in Frobenius inner-product form. -/
theorem frobInner_rsub_smulAp_p
    (P : Problem n M r q)
    (st : PCGState n r)
    (a : Real) :
    frobInner (st.r - a • pcgAp P st) st.p
      = frobInner st.r st.p - a * frobInner (pcgAp P st) st.p := by
  unfold frobInner
  calc
    (st.r - a • pcgAp P st).vec ⬝ᵥ st.p.vec
        = st.p.vec ⬝ᵥ (st.r - a • pcgAp P st).vec := by
            simpa using dotProduct_comm (st.r - a • pcgAp P st).vec st.p.vec
    _ = st.p.vec ⬝ᵥ st.r.vec - st.p.vec ⬝ᵥ (a • pcgAp P st).vec := by
          simp [Matrix.vec_sub, dotProduct_sub]
    _ = st.p.vec ⬝ᵥ st.r.vec - st.p.vec ⬝ᵥ (a • (pcgAp P st).vec) := by
          simp [Matrix.vec_smul]
    _ = st.p.vec ⬝ᵥ st.r.vec - a * (st.p.vec ⬝ᵥ (pcgAp P st).vec) := by
          simp [dotProduct_smul, mul_comm, mul_left_comm, mul_assoc]
    _ = st.r.vec ⬝ᵥ st.p.vec - a * ((pcgAp P st).vec ⬝ᵥ st.p.vec) := by
          simp [dotProduct_comm]

/-- If `α = ⟪r,p⟫/⟪p,Ap⟫` and `⟪p,Ap⟫ ≠ 0`, then
the next residual is orthogonal to the current search direction:
`⟪r⁺, p⟫ = 0`. -/
theorem pcgRNext_search_inner_eq_zero_of_alpha_ratio
    (P : Problem n M r q)
    (st : PCGState n r)
    (hAlpha :
      pcgAlpha P st = frobInner st.r st.p / frobInner st.p (pcgAp P st))
    (hDen : frobInner st.p (pcgAp P st) ≠ 0) :
    frobInner (pcgRNext P st) st.p = 0 := by
  have hComm :
      frobInner (pcgAp P st) st.p = frobInner st.p (pcgAp P st) := by
    unfold frobInner
    simpa using dotProduct_comm (pcgAp P st).vec st.p.vec
  unfold pcgRNext
  calc
    frobInner (st.r - pcgAlpha P st • pcgAp P st) st.p
        = frobInner st.r st.p - pcgAlpha P st * frobInner (pcgAp P st) st.p :=
          frobInner_rsub_smulAp_p (P := P) (st := st) (a := pcgAlpha P st)
    _ = frobInner st.r st.p
          - (frobInner st.r st.p / frobInner st.p (pcgAp P st))
            * frobInner (pcgAp P st) st.p := by rw [hAlpha]
    _ = frobInner st.r st.p
          - (frobInner st.r st.p / frobInner st.p (pcgAp P st))
            * frobInner st.p (pcgAp P st) := by rw [hComm]
    _ = frobInner st.r st.p - frobInner st.r st.p := by
          field_simp [hDen]
    _ = 0 := by ring

/-- Identity-preconditioned orthogonality step:
from `z=r` and `⟪r,p⟫=⟪r,r⟫`, one gets `⟪r⁺,p⟫=0`. -/
theorem pcgRNext_search_inner_eq_zero_of_id
    (P : Problem n M r q)
    (st : PCGState n r)
    (hz : st.z = st.r)
    (hRp : frobInner st.r st.p = frobInner st.r st.r)
    (hDen : frobInner st.p (pcgAp P st) ≠ 0) :
    frobInner (pcgRNext P st) st.p = 0 := by
  have hAlpha :
      pcgAlpha P st = frobInner st.r st.p / frobInner st.p (pcgAp P st) :=
    pcgAlpha_eq_residual_search_ratio_of_z_eq_r (P := P) (st := st) hz hRp
  exact pcgRNext_search_inner_eq_zero_of_alpha_ratio
    (P := P) (st := st) hAlpha hDen

/-- With identity preconditioning, if `⟪r⁺,p⟫=0`, then the next search direction
satisfies `⟪r⁺,p⁺⟫ = ⟪r⁺,r⁺⟫`. -/
theorem pcgRNext_PNext_inner_eq_self_of_id
    (P : Problem n M r q)
    (st : PCGState n r)
    (hOrth : frobInner (pcgRNext P st) st.p = 0) :
    frobInner (pcgRNext P st) (pcgPNext P idPrecond st)
      = frobInner (pcgRNext P st) (pcgRNext P st) := by
  unfold pcgPNext pcgZNext idPrecond
  calc
    frobInner (pcgRNext P st) (pcgRNext P st + pcgBeta P idPrecond st • st.p)
        = frobInner (pcgRNext P st) (pcgRNext P st)
            + pcgBeta P idPrecond st * frobInner (pcgRNext P st) st.p := by
              unfold frobInner
              simp [dotProduct_add, dotProduct_smul, mul_comm, mul_left_comm, mul_assoc]
    _ = frobInner (pcgRNext P st) (pcgRNext P st) := by
          simp [hOrth]

/-- Identity-preconditioned recurrence invariant (under nonzero alpha denominator):
for every iterate, `⟪r_k, p_k⟫ = ⟪r_k, r_k⟫`. -/
theorem pcgRun_id_residual_search_inner_eq_self_of_den_nonzero
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hDen :
      ∀ k : Nat, frobInner (pcgRun P idPrecond x0 k).p
        (pcgAp P (pcgRun P idPrecond x0 k)) ≠ 0) :
    ∀ k : Nat,
      frobInner (pcgRun P idPrecond x0 k).r (pcgRun P idPrecond x0 k).p
        = frobInner (pcgRun P idPrecond x0 k).r (pcgRun P idPrecond x0 k).r := by
  intro k
  induction k with
  | zero =>
      simp [pcgRun, pcgInit, idPrecond, frobInner]
  | succ k ih =>
      let st : PCGState n r := pcgRun P idPrecond x0 k
      have hz : st.z = st.r := by
        simpa [st] using pcgRun_id_z_eq_r (P := P) (x0 := x0) k
      have hOrth :
          frobInner (pcgRNext P st) st.p = 0 := by
        exact pcgRNext_search_inner_eq_zero_of_id
          (P := P) (st := st) (hz := hz)
          (hRp := by simpa [st] using ih)
          (hDen := by simpa [st] using hDen k)
      have hNext :
          frobInner (pcgRNext P st) (pcgPNext P idPrecond st)
            = frobInner (pcgRNext P st) (pcgRNext P st) :=
        pcgRNext_PNext_inner_eq_self_of_id (P := P) (st := st) hOrth
      simpa [pcgRun, pcgStep, st] using hNext

/-- Under the same denominator hypothesis, every next residual is orthogonal to
the current search direction for identity preconditioning:
`⟪r_{k+1}, p_k⟫ = 0`. -/
theorem pcgRun_id_nextResidual_orth_currentSearch_of_den_nonzero
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hDen :
      ∀ k : Nat, frobInner (pcgRun P idPrecond x0 k).p
        (pcgAp P (pcgRun P idPrecond x0 k)) ≠ 0) :
    ∀ k : Nat,
      frobInner (pcgRun P idPrecond x0 (k + 1)).r
        (pcgRun P idPrecond x0 k).p = 0 := by
  intro k
  let st : PCGState n r := pcgRun P idPrecond x0 k
  have hz : st.z = st.r := by
    simpa [st] using pcgRun_id_z_eq_r (P := P) (x0 := x0) k
  have hRp :
      frobInner st.r st.p = frobInner st.r st.r := by
    simpa [st] using
      pcgRun_id_residual_search_inner_eq_self_of_den_nonzero
        (P := P) (x0 := x0) hDen k
  have hOrth :
      frobInner (pcgRNext P st) st.p = 0 := by
    exact pcgRNext_search_inner_eq_zero_of_id
      (P := P) (st := st) (hz := hz) (hRp := hRp)
      (hDen := by simpa [st] using hDen k)
  simpa [pcgRun, pcgStep, st] using hOrth

/-- Under `operatorSPD`, if a state satisfies `⟪r,p⟫ = ⟪r,r⟫` and `r ≠ 0`,
then the alpha denominator is nonzero. -/
theorem pcgAlpha_den_ne_zero_of_operatorSPD_of_rp_eq_rr_of_r_ne_zero
    (P : Problem n M r q)
    (hSPD : operatorSPD P)
    (st : PCGState n r)
    (hRp : frobInner st.r st.p = frobInner st.r st.r)
    (hr : st.r ≠ 0) :
    frobInner st.p (pcgAp P st) ≠ 0 := by
  have hrr_ne : frobInner st.r st.r ≠ 0 := by
    intro h0
    apply hr
    apply Matrix.vec_eq_zero_iff.mp
    exact (dotProduct_self_eq_zero).1 (by simpa [frobInner] using h0)
  have hrp_ne : frobInner st.r st.p ≠ 0 := by
    rw [hRp]
    exact hrr_ne
  have hp : st.p ≠ 0 := by
    intro hp0
    have hRp0 : frobInner st.r st.p = 0 := by
      unfold frobInner
      simp [hp0]
    exact hrp_ne hRp0
  have hPos : 0 < frobInner st.p (pcgAp P st) := by
    simpa [pcgAp] using hSPD st.p hp
  exact ne_of_gt hPos

/-- Identity-preconditioned invariant from the algorithm body and `operatorSPD`
only (no external denominator assumption):
`⟪r_k,p_k⟫ = ⟪r_k,r_k⟫` for every iterate. -/
theorem pcgRun_id_residual_search_inner_eq_self_of_operatorSPD
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hSPD : operatorSPD P) :
    ∀ k : Nat,
      frobInner (pcgRun P idPrecond x0 k).r (pcgRun P idPrecond x0 k).p
        = frobInner (pcgRun P idPrecond x0 k).r (pcgRun P idPrecond x0 k).r := by
  intro k
  induction k with
  | zero =>
      simp [pcgRun, pcgInit, idPrecond, frobInner]
  | succ k ih =>
      let st : PCGState n r := pcgRun P idPrecond x0 k
      have hz : st.z = st.r := by
        simpa [st] using pcgRun_id_z_eq_r (P := P) (x0 := x0) k
      by_cases hr0 : st.r = 0
      · have hAlpha0 : pcgAlpha P st = 0 := by
          exact pcgAlpha_eq_zero_of_z_eq_r_of_r_eq_zero
            (P := P) (st := st) (hz := hz) (hr0 := hr0)
        have hRNext0 : pcgRNext P st = 0 := by
          unfold pcgRNext
          rw [hr0, hAlpha0]
          simp
        have hNext :
            frobInner (pcgRNext P st) (pcgPNext P idPrecond st)
              = frobInner (pcgRNext P st) (pcgRNext P st) := by
          rw [hRNext0]
          simp [frobInner_zero_left]
        simpa [pcgRun, pcgStep, st] using hNext
      · have hDen :
          frobInner st.p (pcgAp P st) ≠ 0 :=
          pcgAlpha_den_ne_zero_of_operatorSPD_of_rp_eq_rr_of_r_ne_zero
            (P := P) (hSPD := hSPD) (st := st)
            (hRp := by simpa [st] using ih) (hr := hr0)
        have hOrth :
            frobInner (pcgRNext P st) st.p = 0 := by
          exact pcgRNext_search_inner_eq_zero_of_id
            (P := P) (st := st) (hz := hz)
            (hRp := by simpa [st] using ih)
            (hDen := hDen)
        have hNext :
            frobInner (pcgRNext P st) (pcgPNext P idPrecond st)
              = frobInner (pcgRNext P st) (pcgRNext P st) :=
          pcgRNext_PNext_inner_eq_self_of_id (P := P) (st := st) hOrth
        simpa [pcgRun, pcgStep, st] using hNext

/-- Identity-preconditioned one-step orthogonality from `operatorSPD` only:
`⟪r_{k+1}, p_k⟫ = 0`. -/
theorem pcgRun_id_nextResidual_orth_currentSearch_of_operatorSPD
    (P : Problem n M r q)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (hSPD : operatorSPD P) :
    ∀ k : Nat,
      frobInner (pcgRun P idPrecond x0 (k + 1)).r
        (pcgRun P idPrecond x0 k).p = 0 := by
  intro k
  let st : PCGState n r := pcgRun P idPrecond x0 k
  have hz : st.z = st.r := by
    simpa [st] using pcgRun_id_z_eq_r (P := P) (x0 := x0) k
  by_cases hr0 : st.r = 0
  · have hAlpha0 : pcgAlpha P st = 0 := by
      exact pcgAlpha_eq_zero_of_z_eq_r_of_r_eq_zero
        (P := P) (st := st) (hz := hz) (hr0 := hr0)
    have hRNext0 : pcgRNext P st = 0 := by
      unfold pcgRNext
      rw [hr0, hAlpha0]
      simp
    simpa [pcgRun, pcgStep, st, hRNext0, frobInner_zero_left]
  · have hRp :
      frobInner st.r st.p = frobInner st.r st.r := by
      simpa [st] using
        pcgRun_id_residual_search_inner_eq_self_of_operatorSPD
          (P := P) (x0 := x0) (hSPD := hSPD) k
    have hDen :
        frobInner st.p (pcgAp P st) ≠ 0 :=
      pcgAlpha_den_ne_zero_of_operatorSPD_of_rp_eq_rr_of_r_ne_zero
        (P := P) (hSPD := hSPD) (st := st) (hRp := hRp) (hr := hr0)
    have hOrth :
        frobInner (pcgRNext P st) st.p = 0 := by
      exact pcgRNext_search_inner_eq_zero_of_id
        (P := P) (st := st) (hz := hz) (hRp := hRp) (hDen := hDen)
    simpa [pcgRun, pcgStep, st] using hOrth

/-- Termination predicate for PCG in at most `K` iterations (`r_K = 0`). -/
def pcgTerminatesWithin (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real) (K : Nat) : Prop :=
  ∃ k : Nat, k ≤ K ∧ (pcgRun P Minv x0 k).r = 0

theorem pcgInit_residual_invariant (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real) :
    (pcgInit P Minv x0).r = rhsMat P - applyA P (pcgInit P Minv x0).x := by
  simp [pcgInit, rhsMat, applyA]

theorem pcgRNext_residual_invariant (P : Problem n M r q)
    (st : PCGState n r)
    (hres : st.r = rhsMat P - applyA P st.x) :
    pcgRNext P st = rhsMat P - applyA P (pcgXNext P st) := by
  unfold pcgRNext pcgXNext pcgAp
  rw [hres, applyA_add, applyA_smul]
  abel

theorem pcgStep_residual_invariant (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (st : PCGState n r)
    (hres : st.r = rhsMat P - applyA P st.x) :
    (pcgStep P Minv st).r = rhsMat P - applyA P (pcgStep P Minv st).x := by
  simpa [pcgStep] using pcgRNext_residual_invariant (P := P) (st := st) hres

/-- Error representation for the next residual:
`r⁺ = A * e⁺` when `xStar` solves `Ax=b`. -/
theorem pcgRNext_eq_applyA_errorNext
    (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real)
    (hRes : st.r = rhsMat P - applyA P st.x)
    (hSol : applyA P xStar = rhsMat P) :
    pcgRNext P st = applyA P (pcgError xStar (pcgStep P Minv st)) := by
  have hResNext :
      pcgRNext P st = rhsMat P - applyA P (pcgXNext P st) :=
    pcgRNext_residual_invariant (P := P) (st := st) hRes
  calc
    pcgRNext P st = rhsMat P - applyA P (pcgXNext P st) := hResNext
    _ = applyA P xStar - applyA P (pcgXNext P st) := by rw [← hSol]
    _ = applyA P (xStar - pcgXNext P st) := by
          symm
          simpa using (applyA_sub_smul (P := P) xStar (pcgXNext P st) (1 : Real))
    _ = applyA P (pcgError xStar (pcgStep P Minv st)) := by
          simp [pcgError, pcgStep, pcgXNext]

/-- One-step `A`-orthogonality of the next error against the current search
direction (identity preconditioning). -/
theorem pcgError_next_Aorth_current_search_of_id
    (P : Problem n M r q)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real)
    (hz : st.z = st.r)
    (hRp : frobInner st.r st.p = frobInner st.r st.r)
    (hDen : frobInner st.p (pcgAp P st) ≠ 0)
    (hRes : st.r = rhsMat P - applyA P st.x)
    (hSol : applyA P xStar = rhsMat P) :
    frobInner (pcgError xStar (pcgStep P idPrecond st)) (pcgAp P st) = 0 := by
  have hOrth : frobInner (pcgRNext P st) st.p = 0 :=
    pcgRNext_search_inner_eq_zero_of_id
      (P := P) (st := st) (hz := hz) (hRp := hRp) (hDen := hDen)
  have hErrNext :
      pcgRNext P st = applyA P (pcgError xStar (pcgStep P idPrecond st)) :=
    pcgRNext_eq_applyA_errorNext
      (P := P) (Minv := idPrecond) (st := st) (xStar := xStar) hRes hSol
  calc
    frobInner (pcgError xStar (pcgStep P idPrecond st)) (pcgAp P st)
        = frobInner st.p (applyA P (pcgError xStar (pcgStep P idPrecond st))) := by
            simpa [pcgAp] using
              (frobInner_applyA_comm
                (P := P)
                (X := pcgError xStar (pcgStep P idPrecond st))
                (Y := st.p))
    _ = frobInner st.p (pcgRNext P st) := by rw [← hErrNext]
    _ = frobInner (pcgRNext P st) st.p := by
          unfold frobInner
          simpa using dotProduct_comm st.p.vec (pcgRNext P st).vec
    _ = 0 := hOrth

/-- Error energy in the `A`-inner product (`‖e‖_A^2` in matrix coordinates). -/
def pcgErrorEnergy (P : Problem n M r q)
    (xStar : Matrix (Fin n) (Fin r) Real) (st : PCGState n r) : Real :=
  frobInner (pcgError xStar st) (applyA P (pcgError xStar st))

/-- One-step monotonicity of `A`-energy for identity-preconditioned CG
under the standard recurrence hypotheses at the current state. -/
theorem pcgErrorEnergy_step_nonincreasing_of_id
    (P : Problem n M r q)
    (st : PCGState n r)
    (xStar : Matrix (Fin n) (Fin r) Real)
    (hSPD : operatorSPD P)
    (hz : st.z = st.r)
    (hRp : frobInner st.r st.p = frobInner st.r st.r)
    (hRes : st.r = rhsMat P - applyA P st.x)
    (hSol : applyA P xStar = rhsMat P)
    (hp : st.p ≠ 0) :
    pcgErrorEnergy P xStar (pcgStep P idPrecond st)
      ≤ pcgErrorEnergy P xStar st := by
  have hMin :=
    pcgAlpha_minimizes_error_energy_along_search_of_id
      (P := P) (st := st) (xStar := xStar)
      (hSPD := hSPD) (hz := hz) (hRp := hRp)
      (hRes := hRes) (hSol := hSol) (hp := hp) (a := 0)
  have hRecurrence :
      pcgError xStar (pcgStep P idPrecond st)
        = pcgError xStar st - pcgAlpha P st • st.p := by
    simpa using pcgError_step (P := P) (Minv := idPrecond) (st := st) (xStar := xStar)
  calc
    pcgErrorEnergy P xStar (pcgStep P idPrecond st)
        = frobInner (pcgError xStar st - pcgAlpha P st • st.p)
            (applyA P (pcgError xStar st - pcgAlpha P st • st.p)) := by
              simp [pcgErrorEnergy, hRecurrence]
    _ ≤ frobInner (pcgError xStar st - (0 : Real) • st.p)
          (applyA P (pcgError xStar st - (0 : Real) • st.p)) := hMin
    _ = pcgErrorEnergy P xStar st := by
          simp [pcgErrorEnergy]

theorem pcgRun_residual_invariant (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat) :
    (pcgRun P Minv x0 iters).r = rhsMat P - applyA P (pcgRun P Minv x0 iters).x := by
  induction iters with
  | zero =>
      simpa [pcgRun] using pcgInit_residual_invariant (P := P) (Minv := Minv) (x0 := x0)
  | succ k ih =>
      simpa [pcgRun] using
        pcgStep_residual_invariant (P := P) (Minv := Minv) (st := pcgRun P Minv x0 k) ih

/-- Monotonicity of `A`-energy along `pcgRun` (identity preconditioning),
assuming the per-step nondegeneracy (`p_k ≠ 0`) needed for `alpha` positivity. -/
theorem pcgRun_id_errorEnergy_nonincreasing
    (P : Problem n M r q)
    (x0 xStar : Matrix (Fin n) (Fin r) Real)
    (hSPD : operatorSPD P)
    (hSol : applyA P xStar = rhsMat P)
    (hSearchNonzero : ∀ k : Nat, (pcgRun P idPrecond x0 k).p ≠ 0) :
    ∀ k : Nat,
      pcgErrorEnergy P xStar (pcgRun P idPrecond x0 (k + 1))
        ≤ pcgErrorEnergy P xStar (pcgRun P idPrecond x0 k) := by
  intro k
  let st : PCGState n r := pcgRun P idPrecond x0 k
  have hz : st.z = st.r := by
    simpa [st] using pcgRun_id_z_eq_r (P := P) (x0 := x0) k
  have hRp :
      frobInner st.r st.p = frobInner st.r st.r := by
    simpa [st] using
      pcgRun_id_residual_search_inner_eq_self_of_operatorSPD
        (P := P) (x0 := x0) (hSPD := hSPD) k
  have hRes : st.r = rhsMat P - applyA P st.x := by
    simpa [st] using pcgRun_residual_invariant (P := P) (Minv := idPrecond) (x0 := x0) k
  have hp : st.p ≠ 0 := by simpa [st] using hSearchNonzero k
  have hMono :
      pcgErrorEnergy P xStar (pcgStep P idPrecond st)
        ≤ pcgErrorEnergy P xStar st :=
    pcgErrorEnergy_step_nonincreasing_of_id
      (P := P) (st := st) (xStar := xStar)
      (hSPD := hSPD) (hz := hz) (hRp := hRp)
      (hRes := hRes) (hSol := hSol) (hp := hp)
  simpa [pcgRun, st] using hMono

/-- Step-1 algorithmic Krylov minimization in `A`-energy (identity preconditioning):
among all degree-`≤1` polynomials with `p(0)=1`, the concrete first `pcgRun`
iterate has no larger `A`-energy error than `p(A)e₀`. -/
theorem pcgRun_id_step1_errorEnergy_min_deg1
    (P : Problem n M r q)
    (x0 xStar : Matrix (Fin n) (Fin r) Real)
    (hSPD : operatorSPD P)
    (hSol : applyA P xStar = rhsMat P)
    (hr0 : pcgR0 P x0 ≠ 0)
    (p : Polynomial Real)
    (hp0 : p.eval 0 = 1)
    (hdeg : p.natDegree ≤ 1) :
    pcgErrorEnergy P xStar (pcgRun P idPrecond x0 1)
      ≤
    frobInner
      (polyApplyLin (applyALin P) p (pcgError xStar (pcgInit P idPrecond x0)))
      (applyA P
        (polyApplyLin (applyALin P) p (pcgError xStar (pcgInit P idPrecond x0)))) := by
  let st0 : PCGState n r := pcgInit P idPrecond x0
  let e0 : Matrix (Fin n) (Fin r) Real := pcgError xStar st0
  have hz : st0.z = st0.r := by
    simp [st0, pcgInit, idPrecond]
  have hRp : frobInner st0.r st0.p = frobInner st0.r st0.r := by
    simp [st0, pcgInit, idPrecond, frobInner]
  have hRes : st0.r = rhsMat P - applyA P st0.x := by
    simpa [st0] using
      (pcgInit_residual_invariant (P := P) (Minv := idPrecond) (x0 := x0))
  have hp : st0.p ≠ 0 := by
    intro hp0'
    have hrInit : st0.r = 0 := by
      simpa [st0, pcgInit, idPrecond] using hp0'
    have hr00 : pcgR0 P x0 = 0 := by
      simpa [pcgR0, st0, pcgInit] using hrInit
    exact hr0 hr00
  have hErr0 : st0.r = applyA P e0 := by
    simpa [e0] using
      (pcgResidual_eq_applyA_error (P := P) (st := st0) (xStar := xStar) hSol hRes)
  have hpEq : st0.p = st0.r := by
    simp [st0, pcgInit, idPrecond]
  have hAe0p : applyA P e0 = st0.p := by
    calc
      applyA P e0 = st0.r := by simpa using hErr0.symm
      _ = st0.p := hpEq.symm
  have hCoeff0 : p.coeff 0 = 1 := by
    calc
      p.coeff 0 = p.eval 0 := by simpa using p.coeff_zero_eq_eval_zero
      _ = 1 := hp0
  have hpForm : p = Polynomial.C (p.coeff 1) * Polynomial.X + (1 : Polynomial Real) := by
    calc
      p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) :=
        Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
      _ = Polynomial.C (p.coeff 1) * Polynomial.X + (1 : Polynomial Real) := by
            simp [hCoeff0]
  let a : Real := -(p.coeff 1)
  have hMin :
      frobInner (e0 - pcgAlpha P st0 • st0.p) (applyA P (e0 - pcgAlpha P st0 • st0.p))
        ≤ frobInner (e0 - a • st0.p) (applyA P (e0 - a • st0.p)) :=
    pcgAlpha_minimizes_error_energy_along_search_of_id
      (P := P) (st := st0) (xStar := xStar)
      (hSPD := hSPD) (hz := hz) (hRp := hRp)
      (hRes := hRes) (hSol := hSol) (hp := hp) (a := a)
  let c : Real := p.coeff 1
  have hpq : p = Polynomial.C c * Polynomial.X + (1 : Polynomial Real) := by
    simpa [c] using hpForm
  have hPoly :
      polyApplyLin (applyALin P) p e0 = e0 - a • st0.p := by
    calc
      polyApplyLin (applyALin P) p e0
          = polyApplyLin (applyALin P)
              (Polynomial.C c * Polynomial.X + (1 : Polynomial Real)) e0 := by
                rw [hpq]
      _ = polyApplyLin (applyALin P) (Polynomial.C c * Polynomial.X) e0
            + polyApplyLin (applyALin P) (1 : Polynomial Real) e0 := by
              simp [polyApplyLin]
      _ = c • applyA P e0 + e0 := by
            simp [polyApplyLin, applyALin, Module.End.mul_apply]
      _ = e0 + c • st0.p := by
            simpa [hAe0p, add_comm, add_left_comm, add_assoc]
      _ = e0 - (-c) • st0.p := by
            simp [sub_eq_add_neg]
      _ = e0 - a • st0.p := by
            simp [a, c]
  have hLeft :
      pcgErrorEnergy P xStar (pcgRun P idPrecond x0 1)
        = frobInner (e0 - pcgAlpha P st0 • st0.p)
            (applyA P (e0 - pcgAlpha P st0 • st0.p)) := by
    have hRecurrence :
        pcgError xStar (pcgRun P idPrecond x0 1)
          = e0 - pcgAlpha P st0 • st0.p := by
      simpa [st0, e0, pcgRun] using
        (pcgError_step (P := P) (Minv := idPrecond) (st := st0) (xStar := xStar))
    simp [pcgErrorEnergy, hRecurrence]
  have hRight :
      frobInner (polyApplyLin (applyALin P) p e0)
          (applyA P (polyApplyLin (applyALin P) p e0))
        = frobInner (e0 - a • st0.p) (applyA P (e0 - a • st0.p)) := by
    simpa [hPoly]
  calc
    pcgErrorEnergy P xStar (pcgRun P idPrecond x0 1)
        = frobInner (e0 - pcgAlpha P st0 • st0.p)
            (applyA P (e0 - pcgAlpha P st0 • st0.p)) := hLeft
    _ ≤ frobInner (e0 - a • st0.p) (applyA P (e0 - a • st0.p)) := hMin
    _ = frobInner (polyApplyLin (applyALin P) p e0)
          (applyA P (polyApplyLin (applyALin P) p e0)) := by
          simpa using hRight.symm

/-- One-step `A`-energy dominance over any affine degree-1 residual candidate
`(1 - aX)(A)e₀` for identity-preconditioned `pcgRun`. -/
theorem pcgRun_id_step1_errorEnergy_le_affineCandidate
    (P : Problem n M r q)
    (x0 xStar : Matrix (Fin n) (Fin r) Real)
    (hSPD : operatorSPD P)
    (hSol : applyA P xStar = rhsMat P)
    (hr0 : pcgR0 P x0 ≠ 0)
    (a : Real) :
    pcgErrorEnergy P xStar (pcgRun P idPrecond x0 1)
      ≤
    frobInner
      (polyApplyLin (applyALin P) (1 - Polynomial.C a * Polynomial.X)
        (pcgError xStar (pcgInit P idPrecond x0)))
      (applyA P
        (polyApplyLin (applyALin P) (1 - Polynomial.C a * Polynomial.X)
          (pcgError xStar (pcgInit P idPrecond x0)))) := by
  have hdeg : (1 - Polynomial.C a * Polynomial.X).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le ?_ ?_
    · simp
    · calc
        (Polynomial.C a * Polynomial.X).natDegree
            ≤ (Polynomial.C a).natDegree + Polynomial.X.natDegree :=
              Polynomial.natDegree_mul_le
        _ = 1 := by simp
  exact pcgRun_id_step1_errorEnergy_min_deg1
    (P := P) (x0 := x0) (xStar := xStar)
    (hSPD := hSPD) (hSol := hSol) (hr0 := hr0)
    (p := (1 - Polynomial.C a * Polynomial.X))
    (hp0 := by simp) (hdeg := hdeg)

theorem pcgRun_matrix_solution_of_zero_residual (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat)
    (hStop : (pcgRun P Minv x0 iters).r = 0) :
    applyA P (pcgRun P Minv x0 iters).x = rhsMat P := by
  have hres := pcgRun_residual_invariant (P := P) (Minv := Minv) (x0 := x0) (iters := iters)
  have hsub : rhsMat P - applyA P (pcgRun P Minv x0 iters).x = 0 := by
    simpa [hres] using hStop
  exact (sub_eq_zero.mp hsub).symm

theorem pcgRun_dense_solution_of_zero_residual (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat)
    (hStop : (pcgRun P Minv x0 iters).r = 0) :
    applyDenseVec P.K P.Z P.Ω P.lam (pcgRun P Minv x0 iters).x.vec = rhsVec P.K P.B := by
  have hsolve := pcgRun_matrix_solution_of_zero_residual
    (P := P) (Minv := Minv) (x0 := x0) (iters := iters) hStop
  exact (q10_system_equiv_matrixFree (K := P.K) (Z := P.Z) (Ω := P.Ω) (lam := P.lam)
      (hK := P.hK) (W := (pcgRun P Minv x0 iters).x) (B := P.B)).2
    (by simpa [applyA, rhsMat] using hsolve)

theorem pcgRun_matrixFreeResidual_zero_of_zero_residual (P : Problem n M r q)
    (Minv : Matrix (Fin n) (Fin r) Real → Matrix (Fin n) (Fin r) Real)
    (x0 : Matrix (Fin n) (Fin r) Real)
    (iters : Nat)
    (hStop : (pcgRun P Minv x0 iters).r = 0) :
    matrixFreeResidual P (pcgRun P Minv x0 iters).x = 0 := by
  unfold matrixFreeResidual
  rw [sub_eq_zero]
  simpa [applyA, rhsMat] using
    pcgRun_matrix_solution_of_zero_residual
      (P := P) (Minv := Minv) (x0 := x0) (iters := iters) hStop

set_option maxHeartbeats 800000 in
theorem pcgRun_one_zeroResidual_ideal (P : Problem n M r q)
    (hPos : (denseMatrix P).PosDef) :
    (pcgRun P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) 1).r = 0 := by
  let st0 : PCGState n r := pcgInit P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real)
  let z0 : Matrix (Fin n) (Fin r) Real := idealMinv P (rhsMat P)
  have hAinv : IsUnit (denseMatrix P).det :=
    (Matrix.isUnit_iff_isUnit_det (denseMatrix P)).mp hPos.isUnit
  have happly0 : applyA P (0 : Matrix (Fin n) (Fin r) Real) = 0 := applyA_zero P
  have hr0 : st0.r = rhsMat P := by
    unfold st0 pcgInit
    simp [happly0]
  have hz0 : st0.z = z0 := by
    unfold st0 z0 pcgInit
    simp [happly0]
  have hp0 : st0.p = z0 := by
    unfold st0 z0 pcgInit
    simp [happly0]
  have hAp0 : pcgAp P st0 = rhsMat P := by
    unfold pcgAp
    rw [hp0]
    simpa [z0] using applyA_idealMinv_eq (P := P) hAinv (rhsMat P)
  have hnumComm : frobInner (rhsMat P) z0 = frobInner z0 (rhsMat P) := by
    unfold frobInner
    simpa using dotProduct_comm (rhsMat P).vec z0.vec
  have hz0_ne_of_rhs_ne : rhsMat P ≠ 0 → z0 ≠ 0 := by
    intro hrhs hz0eq
    apply hrhs
    calc
      rhsMat P = applyA P z0 := by
        simpa [z0] using (applyA_idealMinv_eq (P := P) hAinv (rhsMat P)).symm
      _ = applyA P 0 := by simp [hz0eq]
      _ = 0 := happly0
  have hspd : operatorSPD P := operatorSPD_of_denseMatrix_posDef (P := P) hPos
  have hstep : pcgRNext P st0 = 0 := by
    unfold pcgRNext pcgAlpha pcgAp
    rw [hr0, hz0, hp0]
    have hAzz : applyA P z0 = rhsMat P := by
      simpa [z0] using applyA_idealMinv_eq (P := P) hAinv (rhsMat P)
    rw [hAzz]
    by_cases hrhs : rhsMat P = 0
    · simp [hrhs]
    · have hz0ne : z0 ≠ 0 := hz0_ne_of_rhs_ne hrhs
      have hdpos : 0 < frobInner z0 (rhsMat P) := by
        simpa [hAzz] using hspd z0 hz0ne
      have hdne : frobInner z0 (rhsMat P) ≠ 0 := ne_of_gt hdpos
      have halpha : frobInner (rhsMat P) z0 / frobInner z0 (rhsMat P) = 1 := by
        rw [hnumComm, div_self hdne]
      rw [halpha, one_smul, sub_self]
  unfold pcgRun
  simpa [pcgStep, st0] using hstep

theorem pcgRun_ideal_terminates_within_succ_nr (P : Problem n M r q)
    (hPos : (denseMatrix P).PosDef) :
    ∃ k : Nat, k ≤ n * r + 1 ∧
      (pcgRun P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) k).r = 0 := by
  refine ⟨1, ?_, ?_⟩
  · exact Nat.succ_le_succ (Nat.zero_le (n * r))
  · simpa using pcgRun_one_zeroResidual_ideal (P := P) hPos

theorem pcgRun_ideal_terminates_within_nr (P : Problem n M r q)
    (hPos : (denseMatrix P).PosDef)
    (hn : 0 < n) (hr : 0 < r) :
    ∃ k : Nat, k ≤ n * r ∧
      (pcgRun P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) k).r = 0 := by
  refine ⟨1, ?_, ?_⟩
  · exact Nat.succ_le_of_lt (Nat.mul_pos hn hr)
  · simpa using pcgRun_one_zeroResidual_ideal (P := P) hPos

theorem pcgTerminatesWithin_of_ideal_succ_nr (P : Problem n M r q)
    (hPos : (denseMatrix P).PosDef) :
    pcgTerminatesWithin P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) (n * r + 1) := by
  rcases pcgRun_ideal_terminates_within_succ_nr (P := P) hPos with ⟨k, hk, hstop⟩
  exact ⟨k, hk, hstop⟩

theorem pcgTerminatesWithin_of_ideal_nr (P : Problem n M r q)
    (hPos : (denseMatrix P).PosDef)
    (hn : 0 < n) (hr : 0 < r) :
    pcgTerminatesWithin P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) (n * r) := by
  rcases pcgRun_ideal_terminates_within_nr (P := P) hPos hn hr with ⟨k, hk, hstop⟩
  exact ⟨k, hk, hstop⟩

theorem q10_pcg_ideal_terminatesWithin_nr_certificate
    (P : Problem n M r q)
    (hLam : 0 < P.lam)
    (hKpos : P.K.PosDef)
    (hn : 0 < n) (hr : 0 < r) :
    pcgTerminatesWithin P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) (n * r) ∧
    ∃ k : Nat, k ≤ n * r ∧
      applyDenseVec P.K P.Z P.Ω P.lam
        (pcgRun P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) k).x.vec
          = rhsVec P.K P.B ∧
      matrixFreeResidual P (pcgRun P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) k).x = 0 := by
  have hPos : (denseMatrix P).PosDef := denseMatrix_posDef (P := P) hLam hKpos
  have hTerm : pcgTerminatesWithin P (idealMinv P) (0 : Matrix (Fin n) (Fin r) Real) (n * r) :=
    pcgTerminatesWithin_of_ideal_nr (P := P) hPos hn hr
  refine ⟨hTerm, ?_⟩
  rcases hTerm with ⟨k, hk, hStop⟩
  refine ⟨k, hk, ?_, ?_⟩
  · exact pcgRun_dense_solution_of_zero_residual
      (P := P) (Minv := idealMinv P) (x0 := 0) (iters := k) hStop
  · exact pcgRun_matrixFreeResidual_zero_of_zero_residual
      (P := P) (Minv := idealMinv P) (x0 := 0) (iters := k) hStop


end
end Q10
end AutoProof
