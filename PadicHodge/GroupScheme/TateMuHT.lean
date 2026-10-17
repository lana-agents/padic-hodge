/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateMuZp
import PadicHodge.HodgeTate.Character

/-!
# The Hodge–Tate decomposition for `μ_{p^∞}`

The first case of Tate's Hodge–Tate decomposition for `p`-divisible groups ([BC, §7.2],
discussion after Theorem 7.2.8; [Tate, §4] is not available locally): for `G = μ_{p^∞}`, of
height one and dimension one, `T_p G ⊗ ℂ_p ≅ ℂ_p(1)`.

By `tateMuZpEquiv_gal`, `T_p μ_{p^∞}(ℚ̄_p) ≅ ℤ_p` with `σ ∈ G_L` acting by `χ(σ)`
(`tateMu_charRep`), so `V_p μ_{p^∞} = ℚ_p ⊗ T_p μ_{p^∞}` is the representation `ℚ_p(1)` =
`charRep L 1`, which is Hodge–Tate with the single weight `-1`.
-/

noncomputable section

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- `σ ∈ G_L` acts on `T_p μ_{p^∞}(ℚ̄_p) ⊆ ℚ_p ⊗ T_p μ_{p^∞} ≅ ℚ_p` through `charRep L 1`, i.e.
`V_p μ_{p^∞} ≅ ℚ_p(1)`. -/
theorem tateMu_charRep (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (x : (muPDiv ℚ_[p] p).TateModule (PadicAlgCl p)) :
    ((Multiplicative.toAdd (tateMuZpEquiv (galTate (σ.restrictScalars ℚ_[p]) x)) : ℤ_[p]) :
      ℚ_[p]) =
      charRep L 1 σ ((Multiplicative.toAdd (tateMuZpEquiv x) : ℤ_[p]) : ℚ_[p]) := by
  rw [tateMuZpEquiv_gal, charRep_apply, chiL, chiPow_apply, zpow_one, toAdd_ofAdd,
    PadicInt.coe_mul]

variable {L} [FiniteDimensional ℚ_[p] L]

/-- **Hodge–Tate decomposition for `μ_{p^∞}`**: `V_p μ_{p^∞} ≅ ℚ_p(1)` is Hodge–Tate, i.e.
`T_p μ_{p^∞} ⊗ ℂ_p ≅ ℂ_p(1)`. -/
theorem isHodgeTate_tateMu : IsHodgeTate (charRep L 1) :=
  isHodgeTate_charRep 1

/-- The Hodge–Tate weight of `V_p μ_{p^∞}` is `-1`. -/
theorem htWeights_tateMu : htWeights (charRep L 1) = {-1} :=
  htWeights_charRep 1

end PadicHodge
