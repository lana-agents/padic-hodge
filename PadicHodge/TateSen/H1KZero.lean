/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.TateSen.H1K

/-!
# `H¹(Gal(K_∞/K), \hat K_∞) ≅ K` for a finite extension `K / ℚ_p`

`H1QuotientZeroEquivK : K ≃ₗ[ℚ_p] H¹(Γ_K, \hat K_∞)`, `s ↦ [s log χ]`, where
`Γ_K = G_K / H_K = Gal(K_∞/K)` and `\hat K_∞ = ℂ_p^{H_K}` ([BC, Thm. 14.3.4] and its proof).

Proof as for `K = ℚ_p` (`TateSen/H1GammaZero.lean`): for a cocycle `F` (inflated to `G_K`) write
`F(γ) = γ m - m + r` with `r = ∑ r_i α^i`, `r_i ∈ ℚ_p(μ_{p^N})` (`exists_decomp_K`); then
`(γ - 1) F'(g) = g r - r` for `F' = F - ∂m`, which forces `g r = r` for all `g ∈ G_K`
(`eq_zero_of_autCp_sub_eq_K`), so `r ∈ K`; and `F' - (r / log χ(γ)) log χ` vanishes on `H_K` and
on the powers of `γ`, hence is a coboundary.
-/

noncomputable section

open IntermediateField Topology

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

section Defs

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem rhoK_zero_apply (g : K.fixingSubgroup) (x : ℂ_[p]) :
    rhoK K 0 g x = autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x :=
  cpTwistRepQ_zero_apply _ x

theorem autCp_coe_K (g : K.fixingSubgroup) (s : K) :
    autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (((s : PadicAlgCl p) : ℂ_[p])) =
      ((s : PadicAlgCl p) : ℂ_[p]) := by
  rw [autCp_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).mp g.2 _ s.2]

/-- `K ⊆ ℂ_p^{H_K}`. -/
def kInv : K →ₗ[ℚ_[p]] Representation.invariants ((rhoK K 0).comp (HK K).subtype) where
  toFun s := ⟨((s : PadicAlgCl p) : ℂ_[p]), fun h => by
    change rhoK K 0 (h : K.fixingSubgroup) _ = _
    rw [rhoK_zero_apply, autCp_coe_K]⟩
  map_add' s t := Subtype.ext (by
    change (((s + t : K) : PadicAlgCl p) : ℂ_[p]) =
      ((s : PadicAlgCl p) : ℂ_[p]) + (t : PadicAlgCl p)
    rw [IntermediateField.coe_add, PadicComplex.coe_eq, map_add]; rfl)
  map_smul' c s := Subtype.ext (by
    change (((c • s : K) : PadicAlgCl p) : ℂ_[p]) = c • ((s : PadicAlgCl p) : ℂ_[p])
    rw [IntermediateField.coe_smul, coe_smul_cp])

/-- `log χ` on `Γ_K`. -/
def logChiQK : K.fixingSubgroup ⧸ HK K →* Multiplicative ℚ_[p] :=
  QuotientGroup.lift _ ((logChiHom (p := p)).comp K.fixingSubgroup.subtype) fun h hh => by
    change logChiHom (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) = 1
    rw [← ofAdd_logChi, logChi_eq_zero_of_chi_eq_one (chi_eq_one_of_mem_H
      (mem_H_of_mem_HK ((mem_HK_iff K).mp hh))), ofAdd_zero]

/-- The cocycles `s log χ : Γ_K → K ⊆ ℂ_p^{H_K}`, `s ∈ K`. -/
def logChiCocycleK : K →ₗ[ℚ_[p]] ContH1.cocycles ((rhoK K 0).quotientToInvariants (HK K)) where
  toFun s := ⟨fun x => (logChiQK K x).toAdd • kInv K s, by
    refine ⟨?_, fun x y => ?_⟩
    · refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
      exact ((continuous_logChi (p := p)).comp continuous_subtype_val).smul continuous_const
    · induction x using QuotientGroup.induction_on with | H g => ?_
      induction y using QuotientGroup.induction_on with | H h => ?_
      rw [← QuotientGroup.mk_mul]
      refine Subtype.ext ?_
      change logChi ((g * h : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) •
          ((s : PadicAlgCl p) : ℂ_[p]) =
        logChi (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p]) +
          rhoK K 0 g (logChi (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) •
            ((s : PadicAlgCl p) : ℂ_[p]))
      rw [rhoK_zero_apply, autCp_smul, autCp_coe_K, Subgroup.coe_mul, logChi_mul, add_smul]⟩
  map_add' s t := by
    refine Subtype.ext (funext fun x => ?_)
    change (logChiQK K x).toAdd • kInv K (s + t) =
      (logChiQK K x).toAdd • kInv K s + (logChiQK K x).toAdd • kInv K t
    rw [map_add, smul_add]
  map_smul' c s := by
    refine Subtype.ext (funext fun x => ?_)
    change (logChiQK K x).toAdd • kInv K (c • s) = c • ((logChiQK K x).toAdd • kInv K s)
    rw [map_smul, smul_comm]

theorem infCocycles_logChiCocycleK (s : K) (g : K.fixingSubgroup) :
    (ContH1.infCocycles (rhoK K 0) (HK K) (logChiCocycleK K s) : _ → ℂ_[p]) g =
      logChi (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p]) := rfl

/-- The map `s ↦ [s log χ]`. -/
def logChiClassK : K →ₗ[ℚ_[p]] ContH1.H1 ((rhoK K 0).quotientToInvariants (HK K)) :=
  ContH1.mk _ ∘ₗ logChiCocycleK K

end Defs

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_level (D : CoordData K) (s : K) :
    ∃ c : Fin D.d → PadicAlgCl p, ∃ n1, (∀ i, c i ∈ cycField p n1) ∧
      (s : PadicAlgCl p) = ∑ i, c i * D.α ^ (i : ℕ) := by
  obtain ⟨c, hc, hsc⟩ := D.spans s (le_sup_left (b := cycFieldInf p) s.2)
  choose k hk using fun i => mem_cycFieldInf.mp (hc i)
  exact ⟨c, Finset.univ.sup k, fun i => cycField_mono (Finset.le_sup (Finset.mem_univ i)) (hk i),
    hsc⟩

variable [FiniteDimensional ℚ_[p] K]

set_option maxHeartbeats 1000000 in
-- unfolding the quotient `H¹` of cocycles on the subgroup `G_K` is expensive
theorem logChiClassK_injective : Function.Injective (logChiClassK (p := p) K) := by
  obtain ⟨D⟩ := exists_coordData (K := K)
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [logChiClassK, LinearMap.comp_apply] at hs
  obtain ⟨m, hm⟩ := (ContH1.mk_eq_zero_iff (ρ := (rhoK K 0).quotientToInvariants (HK K))
    (logChiCocycleK K s)).mp hs
  obtain ⟨c, n1, hc, hsc⟩ := exists_level D s
  obtain ⟨γ, hγK, N, hN, u, hu, hγ⟩ := exists_gamma_K K (N0 := max 5 n1) (by omega)
  have hT := isTateGen_of_chi (by omega) hu hγ
  set γK : K.fixingSubgroup := ⟨γ, hγK⟩
  have h1 := congrArg Subtype.val (hm (γK : K.fixingSubgroup ⧸ HK K))
  change logChi γ • ((s : PadicAlgCl p) : ℂ_[p]) = rhoK K 0 γK (m : ℂ_[p]) - m at h1
  rw [rhoK_zero_apply] at h1
  have hmfix : ∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h (m : ℂ_[p]) = m := by
    intro h hh
    have := m.2 ⟨⟨h, mem_GK_of_mem_HK hh⟩, (mem_HK_iff K).mpr hh⟩
    change rhoK K 0 ⟨h, mem_GK_of_mem_HK hh⟩ (m : ℂ_[p]) = m at this
    rwa [rhoK_zero_apply] at this
  have hr : ∀ i, logChi γ • c i ∈ cycField p N := fun i =>
    IntermediateField.smul_mem _ (cycField_mono (by omega) (hc i))
  have h2 : autCp γ (m : ℂ_[p]) - m =
      ∑ i, ((logChi γ • c i : PadicAlgCl p) : ℂ_[p]) * (D.α : ℂ_[p]) ^ (i : ℕ) := by
    rw [← h1, hsc, coe_sum_cp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_smul_cp, smul_mul_assoc]
  have h0 := eq_zero_of_autCp_sub_eq_K D hγK hT (by omega) hmfix hr h2
  have hlog := logChi_ne_zero (by omega) hu hγ
  have hc0 : ∀ i, c i = 0 := fun i => by
    have := h0 i
    rwa [smul_eq_zero, or_iff_right hlog] at this
  apply Subtype.ext
  rw [hsc]
  simp [hc0]

/-- **Key step for `G_K`**: a continuous cocycle `F : G_K → ℂ_p` vanishing on `H_K` with values
in `\hat K_∞` is `s log χ` (`s ∈ K`) up to a coboundary. -/
theorem exists_eq_logChi_add_coboundary_K {F : K.fixingSubgroup → ℂ_[p]}
    (hFc : F ∈ ContH1.cocycles (rhoK K 0)) (hFH : ∀ h : K.fixingSubgroup, h ∈ HK K → F h = 0)
    (hFval : ∀ g, ∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h (F g) = F g) :
    ∃ s : K, ∃ m : ℂ_[p], ∀ g, F g - logChi (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) •
      ((s : PadicAlgCl p) : ℂ_[p]) = autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) m - m := by
  obtain ⟨D⟩ := exists_coordData (K := K)
  have hFmul : ∀ g h, F (g * h) = F g + autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (F h) :=
    fun g h => by rw [hFc.2, rhoK_zero_apply]
  obtain ⟨γ, hγK, N, hN, u, hu, hγ⟩ := exists_gamma_K K (N0 := 5) (by omega)
  have hT := isTateGen_of_chi (by omega) hu hγ
  set γK : K.fixingSubgroup := ⟨γ, hγK⟩
  obtain ⟨m, hm, r, hr, hmr⟩ := exists_decomp_K D hγK hT (by omega) (hFval γK)
  -- `F' = F - ∂m`
  obtain ⟨F', hF'⟩ : ∃ F' : K.fixingSubgroup → ℂ_[p], ∀ g, F' g =
      F g - (autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) m - m) := ⟨_, fun _ => rfl⟩
  have hF'mul : ∀ g h, F' (g * h) =
      F' g + autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (F' h) := fun g h => by
    rw [hF', hF', hF', hFmul, Subgroup.coe_mul, autCp_mul_apply, map_sub, map_sub]
    abel
  have hF'cont : Continuous F' := by
    rw [show F' = fun g => F g - (autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) m - m)
      from funext hF']
    exact hFc.1.sub (((continuous_autCp_apply m).comp continuous_subtype_val).sub
      continuous_const)
  have hF'c : F' ∈ ContH1.cocycles (rhoK K 0) :=
    ⟨hF'cont, fun g h => by rw [hF'mul, rhoK_zero_apply]⟩
  set R : ℂ_[p] := ∑ i, ((r i : PadicAlgCl p) : ℂ_[p]) * (D.α : ℂ_[p]) ^ (i : ℕ) with hR
  have hF'γ : F' γK = R := by
    rw [hF', ← hmr]; abel
  have hF'H : ∀ h : K.fixingSubgroup, h ∈ HK K → F' h = 0 := by
    intro h hh
    rw [hF', hFH h hh, hm _ ((mem_HK_iff K).mp hh), sub_self, sub_zero]
  -- `F'` takes values in `\hat K_∞`
  have hF'fix : ∀ g, ∀ h ∈ (K ⊔ cycFieldInf p).fixingSubgroup, autCp h (F' g) = F' g := by
    intro g h hh
    set hK : K.fixingSubgroup := ⟨h, mem_GK_of_mem_HK hh⟩
    have hhK : hK ∈ HK K := (mem_HK_iff K).mpr hh
    have hc : g⁻¹ * hK * g ∈ HK K := by
      have := Subgroup.Normal.conj_mem (inferInstance : (HK K).Normal) hK hhK g⁻¹
      rwa [inv_inv] at this
    have e1 := hF'mul hK g
    have e2 := hF'mul g (g⁻¹ * hK * g)
    rw [hF'H hK hhK, zero_add] at e1
    rw [hF'H _ hc, map_zero, add_zero, show g * (g⁻¹ * hK * g) = hK * g by group] at e2
    change autCp (hK : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (F' g) = F' g
    rw [← e1, e2]
  -- `g r = r` for all `g ∈ G_K`
  have hrfix : ∀ g : K.fixingSubgroup, ∀ i, (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (r i) =
      r i := by
    intro g
    set c := γK⁻¹ * g⁻¹ * γK * g with hcdef
    have hcH : c ∈ HK K := by
      rw [mem_HK_iff, fixingSubgroup_sup]
      refine ⟨c.2, ?_⟩
      change (c : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (cycFieldInf p).fixingSubgroup
      rw [hcdef]
      simpa using commutator_mem_H (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) γ
    have hcomm : γK * g = g * γK * c := by rw [hcdef]; group
    have e1 : F' (γK * g) = F' g + autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (F' γK) := by
      rw [hcomm, hF'mul, hF'H _ hcH, map_zero, add_zero, hF'mul]
    rw [hF'mul, hF'γ] at e1
    have hαg := autCp_α_of_mem D g.2
    have e2 : autCp γ (F' g) - F' g =
        ∑ i, (((g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (r i) - r i : PadicAlgCl p) : ℂ_[p]) *
          (D.α : ℂ_[p]) ^ (i : ℕ) := by
      have e3 : autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) R =
          ∑ i, (((g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (r i) : PadicAlgCl p) : ℂ_[p]) *
            (D.α : ℂ_[p]) ^ (i : ℕ) := by
        rw [hR, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_pow, hαg, autCp_coe]
      have e4 : autCp γ (F' g) - F' g = autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) R - R := by
        change autCp (γK : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (F' g) - F' g = _
        linear_combination e1
      rw [e4, e3, hR, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coe_sub_cp, sub_mul]
    have hgr : ∀ i, (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (r i) - r i ∈ cycField p N :=
      fun i => sub_mem (gal_mem_cycField _ (hr i)) (hr i)
    intro i
    exact sub_eq_zero.mp (eq_zero_of_autCp_sub_eq_K D hγK hT (by omega) (hF'fix g) hgr e2 i)
  -- hence `r = ∑ r_i α^i ∈ K`
  set r0 : PadicAlgCl p := ∑ i, r i * D.α ^ (i : ℕ) with hr0
  have hr0K : r0 ∈ K := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
    intro g hg
    rw [hr0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hrfix ⟨g, hg⟩ i,
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ D.hα]
  have hR0 : R = ((r0 : PadicAlgCl p) : ℂ_[p]) := by rw [hR, hr0, coe_sum_cp]
  -- subtract `s log χ`
  have hlog0 := logChi_ne_zero (by omega) hu hγ
  set s : K := (logChi γ)⁻¹ • (⟨r0, hr0K⟩ : K) with hs
  have hscoe : ((s : PadicAlgCl p) : ℂ_[p]) = (logChi γ)⁻¹ • ((r0 : PadicAlgCl p) : ℂ_[p]) := by
    rw [hs, IntermediateField.coe_smul, coe_smul_cp]
  have hF''c : (fun g : K.fixingSubgroup => F' g -
      logChi (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p])) ∈
      ContH1.cocycles (rhoK K 0) := by
    refine ⟨hF'c.1.sub (((continuous_logChi (p := p)).comp continuous_subtype_val).smul
      continuous_const), fun g h => ?_⟩
    change F' (g * h) - logChi ((g * h : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) •
        ((s : PadicAlgCl p) : ℂ_[p]) =
      (F' g - logChi (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p])) +
        rhoK K 0 g (F' h - logChi (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) •
          ((s : PadicAlgCl p) : ℂ_[p]))
    rw [hF'mul, rhoK_zero_apply, map_sub, autCp_smul, autCp_coe_K, Subgroup.coe_mul, logChi_mul,
      add_smul]
    abel
  have hF''γ : F' γK - logChi γ • ((s : PadicAlgCl p) : ℂ_[p]) = 0 := by
    rw [hF'γ, hscoe, smul_smul, mul_inv_cancel₀ hlog0, one_smul, hR0, sub_self]
  have hpow : ∀ k : ℕ, F' (γK ^ k) - logChi ((γK ^ k : K.fixingSubgroup) :
      PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p]) = 0 := by
    intro k
    induction k with
    | zero => exact ContH1.cocycle_one _ hF''c
    | succ k ih =>
      have := hF''c.2 (γK ^ k) γK
      beta_reduce at this
      rw [← pow_succ] at this
      rw [this, ih, hF''γ, map_zero, add_zero]
  have hF''H : ∀ h : K.fixingSubgroup, h ∈ HK K →
      F' h - logChi (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p]) =
        0 := by
    intro h hh
    rw [hF'H h hh, logChi_eq_zero_of_chi_eq_one (chi_eq_one_of_mem_H
      (mem_H_of_mem_HK ((mem_HK_iff K).mp hh))), zero_smul, sub_zero]
  have hGN := vanish_of_vanish_pow_K (K := K) (j := 0) (γ := γK) (N := N) (by omega) hu hγ
    hF''c hF''H hpow
  haveI := fixingSubgroup_cycField_subgroupOf_finiteIndex (K := K) (p := p) N
  have hidx : (((cycField p N).fixingSubgroup.subgroupOf K.fixingSubgroup).index : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Subgroup.FiniteIndex.index_ne_zero)
  have h0 := ContH1.mk_eq_zero_of_vanish (rhoK K 0) _ hidx ⟨_, hF''c⟩
    (fun t ht => hGN t (Subgroup.mem_subgroupOf.mp ht))
  rw [ContH1.mk_eq_zero_iff] at h0
  obtain ⟨m', hm'⟩ := h0
  refine ⟨s, m + m', fun g => ?_⟩
  have := hm' g
  rw [rhoK_zero_apply] at this
  change F' g - logChi (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p]) =
    autCp (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) m' - m' at this
  rw [hF'] at this
  rw [map_add]
  linear_combination this

set_option maxHeartbeats 1000000 in
-- unfolding the quotient `H¹` of cocycles on the subgroup `G_K` is expensive
theorem logChiClassK_surjective : Function.Surjective (logChiClassK (p := p) K) := by
  intro x
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨s, m, hm⟩ := exists_eq_logChi_add_coboundary_K
    (ContH1.infCocycles (rhoK K 0) (HK K) f).2
    (fun h hh => infCocycles_K_of_mem f hh) (fun g h hh => infCocycles_K_fixed f g hh)
  have hmH : m ∈ Representation.invariants ((rhoK K 0).comp (HK K).subtype) := by
    rintro ⟨h, hh⟩
    have := hm h
    rw [infCocycles_K_of_mem f hh, logChi_eq_zero_of_chi_eq_one (chi_eq_one_of_mem_H
      (mem_H_of_mem_HK ((mem_HK_iff K).mp hh))), zero_smul, sub_zero, eq_comm,
      sub_eq_zero] at this
    change rhoK K 0 h m = m
    rw [rhoK_zero_apply, this]
  refine ⟨s, ?_⟩
  have key : ContH1.mk ((rhoK K 0).quotientToInvariants (HK K)) (logChiCocycleK K s - f) = 0 := by
    refine (ContH1.mk_eq_zero_iff (ρ := (rhoK K 0).quotientToInvariants (HK K)) _).mpr
      ⟨-⟨m, hmH⟩, fun x => ?_⟩
    induction x using QuotientGroup.induction_on with | H g => ?_
    apply Subtype.ext
    have := hm g
    change logChi (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • ((s : PadicAlgCl p) : ℂ_[p]) -
      (ContH1.infCocycles (rhoK K 0) (HK K) f : _ → ℂ_[p]) g = rhoK K 0 g (-m) - -m
    rw [rhoK_zero_apply, map_neg]
    linear_combination -this
  rw [map_sub, sub_eq_zero] at key
  exact key

/-- **`H¹(Γ_K, \hat K_∞) ≅ K`**: `s ↦ [s log χ]`, `Γ_K = Gal(K_∞/K)`, `K / ℚ_p` finite. -/
def H1QuotientZeroEquivK : K ≃ₗ[ℚ_[p]] ContH1.H1 ((rhoK K 0).quotientToInvariants (HK K)) :=
  LinearEquiv.ofBijective (logChiClassK K) ⟨logChiClassK_injective, logChiClassK_surjective⟩

theorem finrank_H1_quotient_zero_K :
    Module.finrank ℚ_[p] (ContH1.H1 ((rhoK K 0).quotientToInvariants (HK K))) =
      Module.finrank ℚ_[p] K :=
  (H1QuotientZeroEquivK (K := K)).finrank_eq.symm

end PadicHodge
