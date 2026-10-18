/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Lift
import PadicHodge.FormalGroup.LayerSurj
import PadicHodge.FormalGroup.Gm
import PadicHodge.GroupScheme.EtaleUnramified

/-!
# `F(m_{ℂ_p})` is `p`-divisible ([Hong, Prop. 3.2.7], connected case)

For a `p`-divisible formal group law `F` over a local ring `R` (discrete topology, `R → O_{ℂ_p}`
sending the maximal ideal into the open disc), multiplication by `p` on `F(m_{ℂ_p})` is
surjective (`PDivFGL.exists_p_nsmul_eq`), as in the proof of [Hong, Prop. 3.2.7]: the
evaluation `ev_y : A → ℂ_p` lifts along `[p]^*` (`FreeVia.exists_lift`, `ℂ_p` algebraically
closed) to `χ : A → ℂ_p`; `χ(A) ⊆ O_{ℂ_p}` by integrality, `|χ(t_j)| < 1` since
`t_j^N ∈ 𝔪A + [p]^*(I)A` (`tnf_t`), and `χ = ev_x` for `x = (χ(t_j))_j`
(`AdicEval.algHom_ext`, `isHausdorff_span`), so `p · x = y`.

Consequently `log_F : F(m_{ℂ_p}) → ℂ_p^d` is surjective (`PDivFGL.logF_surjective`,
[Hong, Prop. 3.4.7] for `G = F[p^∞]`).
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval

namespace PadicHodge

namespace PDivFGL

universe u

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [IsLocalRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (P : PDivFGL R d p)

omit [IsLocalRing R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] hp in
theorem pSubst_X (j : Fin d) : P.F.pSubst p (X j) = P.F.mulPS p j := by
  rw [FGL.pSubst_apply, subst_X (FGL.hasSubst_of_noConst (P.F.noConst_mulPS p))]

omit [IsLocalRing R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] hp in
theorem pSubst_C (r : R) : P.F.pSubst p (C r) = C r := by
  have := (P.F.pSubst p).commutes r
  rwa [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

/-- **`F(m_{ℂ_p})` is `p`-divisible** ([Hong, Prop. 3.2.7]). -/
theorem exists_p_nsmul_eq
    (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) (y : P.F.Pt p) :
    ∃ x : P.F.Pt p, p • x = y := by
  set φ : MvPowerSeries (Fin d) R →+* MvPowerSeries (Fin d) R := (P.F.pSubst p).toRingHom
  have hφ : FGL.FreeVia φ (p ^ P.height) := P.isPDivisible
  have hn : 0 < p ^ P.height := pow_pos hp.out.pos _
  set yC : MvPowerSeries (Fin d) R →+* ℂ_[p] :=
    (OC p).subtype.comp (P.F.evAlgHom y).toRingHom
  obtain ⟨χ, hχ⟩ := hφ.exists_lift hn yC
  have hχφ : ∀ a, χ (P.F.pSubst p a) = yC a := fun a => congrArg (fun g => g a) hχ
  -- `χ` takes values in `O_{ℂ_p}`
  have hbound : ∀ a, ‖χ a‖ ≤ 1 := by
    intro a
    haveI := hφ.finite
    haveI : Algebra.IsIntegral (MvPowerSeries (Fin d) R) (FGL.ViaRing φ) :=
      Algebra.IsIntegral.of_finite (MvPowerSeries (Fin d) R) (FGL.ViaRing φ)
    letI : Algebra (MvPowerSeries (Fin d) R) ℂ_[p] := yC.toAlgebra
    let χA : FGL.ViaRing φ →ₐ[MvPowerSeries (Fin d) R] ℂ_[p] :=
      { (show FGL.ViaRing φ →+* ℂ_[p] from χ) with
        commutes' := fun r => hχφ r }
    have hint : IsIntegral (MvPowerSeries (Fin d) R) (show FGL.ViaRing φ from a) :=
      Algebra.IsIntegral.isIntegral (R := MvPowerSeries (Fin d) R) (A := FGL.ViaRing φ) _
    exact norm_le_one_of_isIntegral (fun r => (P.F.evAlgHom y r).2) χA hint
  have hC : ∀ r : R, χ (C r) = algebraMap R (OC p) r := by
    intro r
    have e := (P.F.evAlgHom y).commutes r
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at e
    rw [← P.pSubst_C r, hχφ]
    change ((P.F.evAlgHom y (C r) : OC p) : ℂ_[p]) = _
    rw [e]
  let ψ : MvPowerSeries (Fin d) R →ₐ[R] OC p :=
    { toFun := fun a => ⟨χ a, hbound a⟩
      map_one' := Subtype.ext (map_one χ)
      map_mul' := fun a b => Subtype.ext (map_mul χ a b)
      map_zero' := Subtype.ext (map_zero χ)
      map_add' := fun a b => Subtype.ext (map_add χ a b)
      commutes' := fun r => Subtype.ext (by
        change χ (algebraMap R _ r) = _
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hC]) }
  have hψ : ∀ a, (ψ a : ℂ_[p]) = χ a := fun _ => rfl
  -- the coordinates lie in the open disc
  have hball : ∀ a ∈ Ideal.map (algebraMap R (MvPowerSeries (Fin d) R)) (maximalIdeal R) ⊔
      P.F.layerIdeal p 1, ψ a ∈ ballIdeal (p := p) 0 := by
    intro a ha
    have h1 : Ideal.map (algebraMap R (MvPowerSeries (Fin d) R)) (maximalIdeal R) ⊔
        P.F.layerIdeal p 1 ≤ (ballIdeal (p := p) 0).comap ψ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
        simpa [ballIdeal] using hR r hr
      · rw [FGL.layerIdeal, Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, pow_one, ← P.pSubst_X]
        change ‖χ (P.F.pSubst p (X j))‖ < 1 / ((0 : ℕ) + 1 : ℝ)
        rw [hχφ]
        simpa [yC, FGL.evAlgHom_apply, FGL.ev_X] using y.2 j
    exact h1 ha
  have hx : ∀ j, ‖χ (X j)‖ < 1 := by
    intro j
    obtain ⟨N, hN⟩ := P.tnf_t 1 j
    have hN' : (X j : MvPowerSeries (Fin d) R) ^ N ∈
        Ideal.map (algebraMap R (MvPowerSeries (Fin d) R)) (maximalIdeal R) ⊔
          P.F.layerIdeal p 1 := by
      have e : Ideal.map (algebraMap R (P.A 1)) (maximalIdeal R) =
          Ideal.map (Ideal.Quotient.mk (P.F.layerIdeal p 1))
            (Ideal.map (algebraMap R (MvPowerSeries (Fin d) R)) (maximalIdeal R)) := by
        rw [Ideal.map_map]
        rfl
      rw [e] at hN
      have h3 : Ideal.Quotient.mk (P.F.layerIdeal p 1) ((X j : MvPowerSeries (Fin d) R) ^ N) ∈
          Ideal.map (Ideal.Quotient.mk (P.F.layerIdeal p 1))
            (Ideal.map (algebraMap R (MvPowerSeries (Fin d) R)) (maximalIdeal R)) := by
        rw [map_pow]
        exact hN
      exact Ideal.mem_quotient_iff_mem_sup.mp h3
    have h2 := hball _ hN'
    simp only [ballIdeal, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq, map_pow, SubmonoidClass.coe_pow, CharP.cast_eq_zero, zero_add,
      ne_eq, one_ne_zero, not_false_eq_true, div_self, norm_pow, hψ] at h2
    rcases Nat.eq_zero_or_pos N with hN0 | hN0
    · rw [hN0, pow_zero] at h2; exact absurd h2 (lt_irrefl _)
    · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hN0.ne').mp h2
  let X0 : P.F.Pt p := ⟨fun j => ψ (X j), hx⟩
  have key : ψ = P.F.evAlgHom X0 := by
    haveI := isHausdorff_span (fun j => ψ (X j)) hx
    refine AdicEval.algHom_ext (Ideal.span (Set.range fun j => ψ (X j))) (fun i => ?_)
      fun i => ?_
    · exact Ideal.subset_span ⟨i, rfl⟩
    · rw [FGL.evAlgHom_apply, FGL.ev_X]
  refine ⟨X0, P.F.pt_ext fun j => Subtype.ext ?_⟩
  rw [← FGL.ev_mulPS, ← FGL.evAlgHom_apply, ← key, hψ, ← P.pSubst_X, hχφ]
  simp [yC, FGL.evAlgHom_apply, FGL.ev_X]

/-- **`log_F` is surjective** ([Hong, Prop. 3.4.7] for `G = F[p^∞]`). -/
theorem logF_surjective
    (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) (τ : Fin d → ℂ_[p]) :
    ∃ x : P.F.Pt p, ∀ i, P.F.logF x i = τ i :=
  FGL.logF_surjective_of_divisible P.F (P.exists_p_nsmul_eq hR) τ

end PDivFGL

end PadicHodge
