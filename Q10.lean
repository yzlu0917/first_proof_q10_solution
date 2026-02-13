import autoproof.Q10.Mainline

set_option autoImplicit false

open scoped BigOperators Kronecker
open Matrix

namespace AutoProof
namespace Q10

noncomputable section

/-- Final single-file q10.tex delivery entrypoint in `autoproof/Q10.lean`:
includes observed-data-locked RHS/matrix-free equivalence, preconditioners,
PCG residual/rate/cost certificates, online-cost closure, and PSD fallback/shift certificates. -/
abbrev q10_tex_final_answer := @q10_tex_complete_solution_certificate_fully_closed_minimal_spectral

/-- Full d-way final entrypoint (explicit factor/gram witnesses in the interface). -/
abbrev q10_tex_final_answer_full_dway := @q10_tex_complete_solution_certificate_fully_closed_full_dway

/-- PSD-to-SPD closure for PCG in q10.tex style:
for any nugget `nu > 0`, solve shifted kernel system `K + nu I` with PCG guarantees. -/
abbrev q10_tex_final_answer_shifted_pcg := @q10_tex_psd_to_shifted_pcg_certificate

/-- Single closed-loop q10.tex delivery object:
left branch = full PSD-level theorem on original system;
right branch = PSD-to-shifted-PCG theorem (`K + nu I`, `nu > 0`). -/
abbrev q10_tex_final_answer_closed_loop :=
  And.intro
    (@q10_tex_complete_solution_certificate)
    (@q10_tex_psd_to_shifted_pcg_certificate)

/-- Top-level delivery alias (default). -/
abbrev q10_delivery := @q10_tex_complete_solution_certificate_fully_closed_minimal_spectral

/-- Online-closure addendum:
online observed-row PCG cost formulas, interval-to-`kappa` iteration binding, and PSD-to-shift witness. -/
abbrev q10_tex_final_answer_online_closure := @q10_tex_complete_solution_certificate_closed_loop_online

/-- Human-readable tex-aligned overview entrypoint:
paper-order theorem grouping system/RHS/matvec/cost core statements. -/
abbrev q10_tex_final_answer_human_aligned := @q10_tex_human_aligned_default

end
end Q10
end AutoProof
