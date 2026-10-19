/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.OLCompact

/-!
# `O_{K'}` is a discrete valuation ring

`OL L` (`L/ℚ_p` finite inside `ℚ̄_p`) is a local principal ideal domain (`OLCompact.lean`) which
is not a field (`p ∈ 𝔪_L`, `p ≠ 0`), hence a DVR (`OL.instIsDiscreteValuationRing`), as needed to
apply `Fontaine/Monogenic.lean` to extensions `O_E/O_L` ([Fo, Lemme 1]).
-/

namespace PadicHodge

namespace OL

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] L] in
theorem natCast_p_ne_zero : (p : OL L) ≠ 0 := by
  intro h
  have h2 := congrArg nrm h
  rw [nrm_natCast, nrm_zero, norm_eq_zero] at h2
  exact hp.out.ne_zero (by exact_mod_cast h2)

instance instIsDiscreteValuationRing : IsDiscreteValuationRing (OL L) where
  not_a_field' h := by
    have hp' : (p : OL L) ∈ IsLocalRing.maximalIdeal (OL L) := p_mem
    rw [h, Ideal.mem_bot] at hp'
    exact natCast_p_ne_zero hp'

end OL

end PadicHodge
