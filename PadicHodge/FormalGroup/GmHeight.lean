/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.WeierstrassFree
import PadicHodge.FormalGroup.LayerHopf
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# `Ĝ_m` is a `p`-divisible formal group law of height `1`

[Hong, Ex. 2.2.4, Def. 2.2.9]: over a complete local ring `R` with `p ∈ 𝔪_R` (e.g. `ℤ_p`,
`O_K`), `[p]_{Ĝ_m}(t) = (1 + t)^p − 1` (`gm_mulPS`) reduces to `t^p` modulo `𝔪_R`, so by
Weierstrass division (`FormalGroup/WeierstrassFree.lean`) `R[[t]]` is free of rank `p` over
itself via `[p]^*`, with basis `1, t, …, t^{p−1}`: **`Ĝ_m` is `p`-divisible of height `1`**
(`gm_isPDivisible`, `gmPDiv : PDivFGL R 1 p`).

* `FreeVia.of_ringEquiv`: freeness via an endomorphism is transported along ring isomorphisms
  (here `R[[X]] ≃ R[[t_0]]`, `MvPowerSeries.renameEquiv`).
-/

noncomputable section

open MvPowerSeries IsLocalRing

namespace PadicHodge

namespace FGL

theorem FreeVia.of_ringEquiv {B A : Type*} [CommRing B] [CommRing A] (e : B ≃+* A)
    {ψ : B →+* B} {ψ' : A →+* A} (h : ∀ b, e (ψ b) = ψ' (e b)) {n : ℕ} (hψ : FreeVia ψ n) :
    FreeVia ψ' n := by
  obtain ⟨b, hb⟩ := hψ
  refine ⟨fun i => e (b i), ?_⟩
  have E : (fun c : Fin n → A => ∑ i, ψ' (c i) * e (b i)) =
      e ∘ (fun c : Fin n → B => ∑ i, ψ (c i) * b i) ∘ (fun c i => e.symm (c i)) := by
    funext c
    simp only [Function.comp_apply, map_sum, map_mul, h, RingEquiv.apply_symm_apply]
  rw [E]
  refine e.bijective.comp (hb.comp ⟨fun c c' hc => funext fun i => ?_, fun c =>
    ⟨fun i => e (c i), funext fun i => by simp⟩⟩)
  simpa using congrFun hc i

variable {R : Type*} [CommRing R]

/-- **`[n]_{Ĝ_m}(t) = (1 + t)^n − 1`.** -/
theorem gm_mulPS (n : ℕ) :
    (multiplicative R).mulPS n 0 = (1 + X 0) ^ n - 1 := by
  induction n with
  | zero => simp [mulPS_zero]
  | succ n ih =>
    rw [mulPS_succ, addPS]
    change (multΦ R).subst _ = _
    rw [subst_multΦ_pairFam ((multiplicative R).noConst_mulPS n) noConst_X]
    change (multiplicative R).mulPS n 0 + X 0 + (multiplicative R).mulPS n 0 * X 0 = _
    rw [ih]
    ring

/-- `R[[X]] ≃ R[[t_0]]`. -/
abbrev fin1Equiv : PowerSeries R ≃ₐ[R] MvPowerSeries (Fin 1) R :=
  renameEquiv R finOneEquiv.symm

theorem fin1Equiv_apply (f : PowerSeries R) :
    fin1Equiv f = PowerSeries.subst (X 0 : MvPowerSeries (Fin 1) R) f := by
  change rename _ f = _
  rw [rename_eq_subst, PowerSeries.subst_def]
  rfl

/-- `(1 + X)^p − 1 ∈ R[[X]]`. -/
abbrev gmP (p : ℕ) : PowerSeries R := (1 + PowerSeries.X) ^ p - 1

theorem constantCoeff_gmP (p : ℕ) : PowerSeries.constantCoeff (gmP (R := R) p) = 0 := by
  simp [gmP]

theorem fin1Equiv_psi (p : ℕ) (f : PowerSeries R) :
    fin1Equiv (PowerSeries.subst (gmP (R := R) p) f) =
      (multiplicative R).pSubst p (fin1Equiv f) := by
  have hg := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_gmP (R := R) p)
  have hX : PowerSeries.HasSubst (X 0 : MvPowerSeries (Fin 1) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X _)
  have hm := hasSubst_of_noConst ((multiplicative R).noConst_mulPS p)
  rw [fin1Equiv_apply, fin1Equiv_apply, pSubst_apply, PowerSeries.subst_comp_subst_apply hg hX]
  simp only [PowerSeries.subst_def]
  rw [subst_comp_subst_apply hX.const hm]
  congr 2
  funext _
  rw [subst_X hm, gm_mulPS, ← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom hX]
  simp only [gmP, map_sub, map_pow, map_add, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hX]

variable [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

omit [IsAdicComplete (maximalIdeal R) R] in
theorem map_gmP (p : ℕ) [hp : Fact p.Prime] (hpR : (p : R) ∈ maximalIdeal R) :
    (gmP (R := R) p).map (residue R) = PowerSeries.X ^ p := by
  haveI : CharP (ResidueField R) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (residue R), residue_eq_zero_iff]; exact hpR)
  haveI : CharP (PowerSeries (ResidueField R)) p :=
    charP_of_injective_algebraMap PowerSeries.C_injective p
  simp only [gmP, map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
  rw [add_comm, add_pow_char, one_pow, add_sub_cancel_right]

/-- **`Ĝ_m` is `p`-divisible of height `1`** over a complete local ring with `p ∈ 𝔪`. -/
theorem gm_isPDivisible (p : ℕ) [hp : Fact p.Prime] (hpR : (p : R) ∈ maximalIdeal R) :
    (multiplicative R).IsPDivisible p 1 := by
  have hm := map_gmP p hpR
  have hne : (gmP (R := R) p).map (residue R) ≠ 0 := by
    rw [hm]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  have h := WeierstrassFree.freeVia_psi (hg0 := constantCoeff_gmP p) hne p (by
    rw [hm, PowerSeries.order_X_pow]; rfl)
  rw [IsPDivisible, pow_one]
  refine FreeVia.of_ringEquiv fin1Equiv.toRingEquiv (fun b => ?_) h
  change fin1Equiv (PowerSeries.substAlgHom _ b) = _
  rw [PowerSeries.coe_substAlgHom, fin1Equiv_psi]
  rfl

end FGL

/-- **`Ĝ_m` as a `p`-divisible formal group law of height `1`.** -/
def gmPDiv (R : Type*) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [Fact p.Prime] (hpR : (p : R) ∈ maximalIdeal R) : PDivFGL R 1 p where
  F := FGL.multiplicative R
  height := 1
  isPDivisible := FGL.gm_isPDivisible p hpR

end PadicHodge
