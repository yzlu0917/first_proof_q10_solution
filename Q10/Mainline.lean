import autoproof.Q10.Mainline.Entry
import autoproof.Q10.Mainline.TexAnswer
import autoproof.Q10.Mainline.TexAligned

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

/-- Unique delivery entrypoint of the refactored q10 mainline
(minimal-input spectral-indexed default theorem interface). -/
abbrev q10_mainline_delivery := @q10_tex_complete_solution_certificate_fully_closed_minimal_spectral

/-- Legacy strict-Loewner mainline entrypoint retained for compatibility. -/
abbrev q10_mainline_delivery_loewner_legacy := @q10_tex_mainline_theorem

/-- q10.tex-style integrated delivery entrypoint (minimal-input spectral-indexed default). -/
abbrev q10_mainline_tex_answer_delivery := @q10_tex_complete_solution_certificate_fully_closed_minimal_spectral

/-- q10.tex-style integrated delivery entrypoint (full d-way, explicit witnesses). -/
abbrev q10_mainline_tex_answer_delivery_full_dway := @q10_tex_complete_solution_certificate_fully_closed_full_dway

/-- q10.tex full-scope integrated delivery entrypoint (SPD-PCG branch explicit). -/
abbrev q10_mainline_full_delivery := @q10_tex_full_solution_certificate

/-- q10.tex perfect-fit delivery entrypoint (observed-data-locked + CSR/factor-gram/sqrt-rate). -/
abbrev q10_mainline_perfect_delivery := @q10_tex_perfect_solution_certificate

/-- q10.tex problem-style (minimal-assumption) integrated delivery entrypoint. -/
abbrev q10_mainline_problem_style_delivery := @q10_tex_problem_style_solver_certificate

/-- q10.tex unified final delivery entrypoint:
complete PSD-level answer plus shifted-PCG closure (`K + nu I`, `nu > 0`). -/
abbrev q10_mainline_unified_final_delivery := @q10_tex_complete_solution_certificate_fully_closed_minimal_spectral

/-- q10.tex online-closure addendum delivery entrypoint
(online observed-row PCG cost + interval-to-`kappa` binding + PSD-to-shift witness). -/
abbrev q10_mainline_online_closure_delivery := @q10_tex_complete_solution_certificate_closed_loop_online

/-- q10.tex unified shifted-PCG delivery entrypoint under PSD kernel (`nu > 0`). -/
abbrev q10_mainline_unified_shifted_pcg_delivery := @q10_tex_psd_to_shifted_pcg_certificate

/-- Human-readable q10.tex-aligned entrypoint:
paper-order overview theorem for side-by-side tex/Lean reading. -/
abbrev q10_mainline_human_aligned_delivery := @q10_tex_human_aligned_default

end
end Q10
end AutoProof
