/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Basic

/-!
# Powers of the cyclotomic character are Hodge–Tate

`ℚ_p(j)`, the line `ℚ_p` with `G_L` acting through `χ^j`, is Hodge–Tate with the single weight
`-j` (the convention of [BC, §2.3]: `ℂ_p(q)` has weight `-q`): `1 ⊗ 1 ∈ ℂ_p ⊗ ℚ_p(j)` spans
`D_{-j}`.

* `charRep L j`, `isHodgeTate_charRep`, `htWeights_charRep : htWeights (charRep L j) = {-j}`.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- `ℚ_p(j)`: the line `ℚ_p` with `σ` acting by `χ(σ)^j`. -/
def charRep (j : ℤ) : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) ℚ_[p] where
  toFun σ := chiL L j σ • LinearMap.id
  map_one' := by rw [chiL_one, one_smul]; rfl
  map_mul' σ τ := by
    rw [chiL_mul, mul_smul]
    ext
    simp [mul_comm]

theorem charRep_apply (j : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℚ_[p]) :
    charRep L j σ x = chiL L j σ * x := rfl

variable {L} [FiniteDimensional ℚ_[p] L]

theorem one_tmul_one_mem_DHT (j : ℤ) :
    (show CpTensor (charRep L j) from (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p])) ∈
      DHT (charRep L j) (-j) := by
  have key : ∀ σ, TensorProduct.map (galCpLin L σ) (charRep L j σ)
      ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p])) =
      (algebraMap ℚ_[p] ℂ_[p] (chiL L j σ)) • ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p])) := by
    intro σ
    rw [TensorProduct.map_tmul, galCpLin_apply, map_one, charRep_apply, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [mem_DHT]
  intro σ
  refine (key σ).trans ?_
  change _ = (algebraMap L ℂ_[p] (algebraMap ℚ_[p] L (chiL L (-(-j)) σ))) •
    ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p]))
  rw [neg_neg, algebraMap_L_cp_algebraMap]

/-- `ℚ_p(j)` is Hodge–Tate. -/
theorem isHodgeTate_charRep (j : ℤ) : IsHodgeTate (charRep L j) := by
  rw [isHodgeTate_iff_exists_basis]
  refine ⟨Unit, inferInstance, (Basis.singleton Unit ℚ_[p]).baseChange ℂ_[p], fun _ => -j,
    fun i => ?_⟩
  cases i
  have hb : (Basis.singleton Unit ℚ_[p]).baseChange ℂ_[p] () =
      (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p]) := by
    simp
  exact (congrArg (fun w => w ∈ DHT (charRep L j) (-j)) hb).mpr (one_tmul_one_mem_DHT j)

/-- The Hodge–Tate weight of `ℚ_p(j)` is `-j`. -/
theorem htWeights_charRep (j : ℤ) : htWeights (charRep L j) = {-j} := by
  have hcard : Multiset.card (htWeights (charRep L j)) = 1 := by
    rw [(isHodgeTate_iff_card_htWeights _).1 (isHodgeTate_charRep j), finrank_self]
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 hcard
  have hpos : 0 < (htWeights (charRep L j)).count (-j) := by
    rw [count_htWeights, Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨_, one_tmul_one_mem_DHT j⟩, fun h => ?_⟩
    have h1 := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at h1
    refine ((Basis.singleton Unit ℚ_[p]).baseChange ℂ_[p]).ne_zero () ?_
    have hb : (Basis.singleton Unit ℚ_[p]).baseChange ℂ_[p] () =
        (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] (1 : ℚ_[p]) := by
      simp
    exact hb.trans h1
  rw [ha] at hpos ⊢
  rw [Multiset.count_singleton] at hpos
  split_ifs at hpos with h
  · rw [h]
  · exact absurd hpos (lt_irrefl 0)

end PadicHodge
