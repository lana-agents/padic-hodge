/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.TateSen.Coord

/-!
# `H¹(Gal(K_∞/K), \hat K_∞(j))` for a finite extension `K / ℚ_p`

Let `K / ℚ_p` be finite, `K_∞ = K(μ_{p^∞})`, `G_K = Gal(ℚ̄_p/K)` (realised as the closed subgroup
`K.fixingSubgroup` of `Gal(ℚ̄_p/ℚ_p)`), `H_K = Gal(ℚ̄_p/K_∞)` and `Γ_K = G_K / H_K`. By
Ax–Sen–Tate, `ℂ_p^{H_K} = \hat K_∞`.

* `subsingleton_H1_quotient_twist_K`: `H¹(Γ_K, \hat K_∞(j)) = 0` for `j ≠ 0`;
* `H1QuotientZeroEquivK : K ≃ₗ[ℚ_p] H¹(Γ_K, \hat K_∞)`, `s ↦ [s log χ]`.

([BC, Thm. 14.3.4] and its proof, for the cyclotomic character.) The proofs are those of
`TateSen/H1GammaMain.lean` and `TateSen/H1GammaZero.lean`, using the coordinates of
`TateSen/Coord.lean` on `\hat K_∞` and an element `γ ∈ G_K` with `χ(γ) = 1 + p^N u`
(`exists_gamma_K`).
-/

noncomputable section

open IntermediateField Topology

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### An element `γ ∈ G_K` with `χ(γ) = 1 + p^N u` -/

theorem isUnit_natCast_of_not_dvd {c : ℕ} (hc : ¬ p ∣ c) : IsUnit (c : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hc ?_)
  rw [PadicInt.norm_lt_one_iff_dvd] at h
  obtain ⟨w, hw⟩ := h
  have := congrArg (PadicInt.toZMod (p := p)) hw
  rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul] at this
  exact (ZMod.natCast_eq_zero_iff c p).mp this

/-- `(1 + p^M v)^c = 1 + p^M w` with `w` a unit, for `v` a unit and `p ∤ c`. -/
theorem one_add_pow_of_not_dvd {M : ℕ} (hM : 1 ≤ M) {v : ℤ_[p]} (hv : IsUnit v) {c : ℕ}
    (hc : ¬ p ∣ c) : ∃ w : ℤ_[p], IsUnit w ∧
      (1 + (p : ℤ_[p]) ^ M * v) ^ c = 1 + (p : ℤ_[p]) ^ M * w := by
  set x := (p : ℤ_[p]) ^ M * v with hx
  obtain ⟨r, hr⟩ := sq_dvd_add_pow_sub_sub x (1 : ℤ_[p]) c
  simp only [one_pow, one_mul] at hr
  have hsmall : ‖(p : ℤ_[p]) ^ M * v * r‖ < 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    rw [pow_succ', mul_assoc, mul_assoc]
    exact norm_p_mul_lt_one _
  refine ⟨v * (c + (p : ℤ_[p]) ^ M * v * r),
    hv.mul (isUnit_add_of_norm_lt (isUnit_natCast_of_not_dvd hc) hsmall), ?_⟩
  rw [add_comm (1 : ℤ_[p]) x]
  linear_combination hr

/-- There is `γ ∈ G_K` with `χ(γ) = 1 + p^N u`, `N ≥ N₀`, `u` a unit. -/
theorem exists_gamma_K (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {N0 : ℕ} (hN0 : 2 ≤ N0) :
    ∃ γ ∈ K.fixingSubgroup, ∃ N, N0 ≤ N ∧ ∃ u : ℤ_[p], IsUnit u ∧
      ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ N * u := by
  obtain ⟨γ0, u0, hu0, hγ0⟩ := exists_chi_eq (p := p) N0 (by omega)
  haveI := fixingSubgroup_finiteIndex K
  haveI : Finite ((PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ K.fixingSubgroup) :=
    Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨i0, j0, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => ((γ0 ^ (p ^ i) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ K.fixingSubgroup))
  -- wlog `i < j`
  obtain ⟨i, j, hij, hmem⟩ : ∃ i j, i < j ∧
      (γ0 ^ (p ^ i))⁻¹ * γ0 ^ (p ^ j) ∈ K.fixingSubgroup := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i0, j0, h, QuotientGroup.eq.mp heq⟩
    · exact ⟨j0, i0, h, QuotientGroup.eq.mp heq.symm⟩
  set a := γ0 ^ (p ^ i) with ha
  set q := p ^ (j - i) with hq
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.out.pos
  have hpow : γ0 ^ (p ^ j) = a ^ q := by
    rw [ha, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hij.le]
  have hγ : a⁻¹ * γ0 ^ (p ^ j) = a ^ (q - 1) := by
    rw [hpow, show q = (q - 1) + 1 by omega, pow_succ', inv_mul_cancel_left, Nat.add_sub_cancel]
  rw [hγ] at hmem
  obtain ⟨u1, hu1, h1⟩ := one_add_pow_p_pow hN0 hu0 i
  have hc : ¬ p ∣ q - 1 := by
    intro hd
    have h2 : p ∣ q := dvd_pow_self p (by omega)
    have := (Nat.dvd_sub_iff_right (by omega) h2).mpr hd
    rw [show q - (q - 1) = 1 by omega] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨w, hw, h2⟩ := one_add_pow_of_not_dvd (M := N0 + i) (by omega) hu1 hc
  refine ⟨a ^ (q - 1), hmem, N0 + i, by omega, w, hw, ?_⟩
  rw [map_pow, Units.val_pow_eq_pow_val, ha, map_pow, Units.val_pow_eq_pow_val, hγ0, h1, h2]

theorem chiPow_props' {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {N : ℕ} (hN : 5 ≤ N)
    {u : ℤ_[p]} (hu : IsUnit u)
    (hγ : ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ N * u) {j : ℤ} (hj : j ≠ 0) :
    ((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) ≠ 1 ∧
      (p : ℝ) ^ 4 * ‖((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ < 1 := by
  constructor
  · intro h
    apply zpow_ne_one (by omega : 2 ≤ N) hu hγ hj
    rw [chiPow_apply] at h
    exact Subtype.ext (h.trans PadicInt.coe_one.symm)
  · have h1 : ‖((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ ≤ ‖((chi γ : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ := by
      rw [chiPow_apply]
      have := norm_zpow_sub_one_le (chi γ) j
      rw [← PadicInt.padic_norm_e_of_padicInt] at this
      push_cast at this
      exact this
    rw [hγ, add_sub_cancel_left, norm_mul, norm_pow, PadicInt.norm_p,
      PadicInt.isUnit_iff.mp hu, mul_one] at h1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have h5 : (p : ℝ)⁻¹ ^ N ≤ (p : ℝ)⁻¹ ^ 5 :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp1.le) hN
    calc (p : ℝ) ^ 4 * ‖((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ 4 * ((p : ℝ)⁻¹ ^ 5) :=
          mul_le_mul_of_nonneg_left (h1.trans h5) (by positivity)
      _ = (p : ℝ)⁻¹ := by field_simp
      _ < 1 := inv_lt_one_of_one_lt₀ hp1

/-! ### The groups `G_K ⊇ H_K` -/

section Groups

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- `H_K = Gal(ℚ̄_p/K_∞)` as a subgroup of `G_K`. -/
abbrev HK : Subgroup K.fixingSubgroup :=
  (K ⊔ cycFieldInf p).fixingSubgroup.subgroupOf K.fixingSubgroup

instance normal_HK : (HK K).Normal := by
  constructor
  intro h hh g
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [fixingSubgroup_sup] at hh ⊢
  refine ⟨(g * h * g⁻¹).2, ?_⟩
  have := (normal_fixingSubgroup_cycFieldInf (p := p)).conj_mem _ hh.2 g
  simpa using this

/-- `ℂ_p(j)` as a representation of `G_K`. -/
abbrev rhoK (j : ℤ) : Representation ℚ_[p] K.fixingSubgroup ℂ_[p] :=
  (cpTwistRepQ (p := p) j).comp K.fixingSubgroup.subtype

theorem mem_HK_iff {h : K.fixingSubgroup} :
    h ∈ HK K ↔ (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (K ⊔ cycFieldInf p).fixingSubgroup :=
  Subgroup.mem_subgroupOf

theorem compactSpace_GK : CompactSpace K.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed K).isCompact

end Groups

section Cocycles

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- A continuous function on `G_K` vanishing on `H_K` is small on `G_K ∩ Gal(ℚ̄_p/ℚ_p(μ_{p^N}))`
for `N` large. -/
theorem exists_small_on_K {F : K.fixingSubgroup → ℂ_[p]} (hc : Continuous F)
    (hH : ∀ h : K.fixingSubgroup, h ∈ HK K → F h = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ τ : K.fixingSubgroup, (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈
      (cycField p N).fixingSubgroup → ‖F τ‖ < ε := by
  haveI := compactSpace_GK K
  by_contra hne
  push Not at hne
  set t : ℕ → Set K.fixingSubgroup := fun N =>
    {τ | (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (cycField p N).fixingSubgroup} ∩
      {τ | ε ≤ ‖F τ‖} with ht
  have hanti : ∀ {a b : ℕ}, a ≤ b → t b ⊆ t a := by
    intro a b hab τ hτ
    exact ⟨fixingSubgroup_antitone (cycField_mono hab) hτ.1, hτ.2⟩
  have hdir : Directed (· ⊇ ·) t := fun a b =>
    ⟨max a b, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩
  have hne' : ∀ N, (t N).Nonempty := fun N => by
    obtain ⟨τ, hτ, hτε⟩ := hne N
    exact ⟨τ, hτ, hτε⟩
  have hcl : ∀ N, IsClosed (t N) := fun N => by
    haveI := finiteDimensional_cycField (p := p) N
    exact ((IntermediateField.fixingSubgroup_isClosed _).preimage continuous_subtype_val).inter
      (isClosed_le continuous_const hc.norm)
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne'
    (fun N => (hcl N).isCompact) hcl
  rw [Set.mem_iInter] at hτ
  have hτH : τ ∈ HK K := by
    rw [mem_HK_iff, fixingSubgroup_sup]
    refine ⟨τ.2, ?_⟩
    change (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (cycFieldInf p).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨k, hk⟩ := mem_cycFieldInf.mp hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (hτ k).1 x hk
  have := (hτ 0).2
  simp only [Set.mem_setOf_eq, hH τ hτH, norm_zero] at this
  linarith

/-- A cocycle for `ℂ_p(j)` on `G_K` vanishing on `H_K` and on all powers of `γ`
(`χ(γ) = 1 + p^N u`) vanishes on `G_K ∩ Gal(ℚ̄_p/ℚ_p(μ_{p^N}))`. -/
theorem vanish_of_vanish_pow_K {j : ℤ} {γ : K.fixingSubgroup} {N : ℕ} (hN : 2 ≤ N)
    {u : ℤ_[p]} (hu : IsUnit u)
    (hγ : ((chi (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℤ_[p]ˣ) : ℤ_[p]) =
      1 + (p : ℤ_[p]) ^ N * u)
    {F' : K.fixingSubgroup → ℂ_[p]} (hF'c : F' ∈ ContH1.cocycles (rhoK K j))
    (hF'H : ∀ h : K.fixingSubgroup, h ∈ HK K → F' h = 0) (hpow : ∀ k : ℕ, F' (γ ^ k) = 0) :
    ∀ σ : K.fixingSubgroup, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈
      (cycField p N).fixingSubgroup → F' σ = 0 := by
  intro σ hσ
  by_contra hne
  have hε : 0 < ‖F' σ‖ := norm_pos_iff.mpr hne
  obtain ⟨N0, hN0⟩ := exists_small_on_K hF'c.1 hF'H hε
  set M := max N0 N with hM
  obtain ⟨k, hk⟩ := exists_pow_dvd_sub hN hu (dvd_chi_sub_one_of_mem hσ) (le_max_right N0 N)
  rw [← hγ] at hk
  set τ := (γ ^ k)⁻¹ * σ with hτ
  have hτN : (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (cycField p M).fixingSubgroup := by
    refine mem_of_dvd_chi_sub_one (by omega) ?_
    have e : ((chi (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℤ_[p]ˣ) : ℤ_[p]) - 1 =
        (((chi (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ^ k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
          (((chi (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℤ_[p]ˣ) : ℤ_[p]) -
            ((chi (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ^ k : ℤ_[p]ˣ) : ℤ_[p])) := by
      rw [hτ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul, map_inv, map_pow,
        mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [e, Units.val_pow_eq_pow_val]
    exact Dvd.dvd.mul_left hk _
  have hστ : σ = γ ^ k * τ := by rw [hτ, mul_inv_cancel_left]
  have h1 : F' σ = rhoK K j (γ ^ k) (F' τ) := by
    rw [hστ, hF'c.2, hpow, zero_add]
  have h2 : ‖F' τ‖ < ‖F' σ‖ := hN0 τ (fixingSubgroup_antitone
    (cycField_mono (le_max_left N0 N)) hτN)
  rw [h1] at h2
  change ‖F' τ‖ < ‖cpTwistRepQ j ((γ ^ k : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (F' τ)‖ at h2
  rw [norm_cpTwistRepQ] at h2
  exact lt_irrefl _ h2

theorem cpTwistRepQ_of_mem_HK (j : ℤ) {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hh : h ∈ (K ⊔ cycFieldInf p).fixingSubgroup) (x : ℂ_[p]) :
    cpTwistRepQ j h x = autCp h x :=
  cpTwistRepQ_of_mem_H j (mem_H_of_mem_HK hh) x

/-- An inflated cocycle vanishes on `H_K`. -/
theorem infCocycles_K_of_mem {j : ℤ}
    (f : ContH1.cocycles ((rhoK K j).quotientToInvariants (HK K)))
    {h : K.fixingSubgroup} (hh : h ∈ HK K) :
    (ContH1.infCocycles _ _ f : K.fixingSubgroup → ℂ_[p]) h = 0 := by
  change ((f : _ → Representation.invariants ((rhoK K j).comp (HK K).subtype))
      (QuotientGroup.mk h : K.fixingSubgroup ⧸ HK K) : ℂ_[p]) = 0
  rw [(QuotientGroup.eq_one_iff h).mpr hh, ContH1.cocycle_one _ f.2]
  rfl

/-- An inflated cocycle takes values in `ℂ_p^{H_K} = \hat K_∞`. -/
theorem infCocycles_K_fixed {j : ℤ}
    (f : ContH1.cocycles ((rhoK K j).quotientToInvariants (HK K))) (g : K.fixingSubgroup)
    {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hh : h ∈ (K ⊔ cycFieldInf p).fixingSubgroup) :
    autCp h ((ContH1.infCocycles _ _ f : K.fixingSubgroup → ℂ_[p]) g) =
      (ContH1.infCocycles _ _ f : K.fixingSubgroup → ℂ_[p]) g := by
  have hGK : h ∈ K.fixingSubgroup := mem_GK_of_mem_HK hh
  have := ((f : _ → Representation.invariants ((rhoK K j).comp (HK K).subtype))
    (QuotientGroup.mk g : K.fixingSubgroup ⧸ HK K)).2
      ⟨⟨h, hGK⟩, (mem_HK_iff K).mpr hh⟩
  rw [← cpTwistRepQ_of_mem_HK j hh]
  exact this

theorem fixingSubgroup_cycField_subgroupOf_finiteIndex (N : ℕ) :
    ((cycField p N).fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex := by
  haveI := fixingSubgroup_cycField_finiteIndex (p := p) N
  infer_instance

end Cocycles

section Main

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]

set_option maxHeartbeats 1000000 in
-- unfolding the quotient `H¹` of cocycles on the subgroup `G_K` is expensive
/-- **`H¹(Γ_K, \hat K_∞(j)) = 0` for `j ≠ 0`**, `Γ_K = Gal(K_∞/K)`. -/
theorem subsingleton_H1_quotient_twist_K {j : ℤ} (hj : j ≠ 0) :
    Subsingleton (ContH1.H1 ((rhoK K j).quotientToInvariants (HK K))) := by
  obtain ⟨D⟩ := exists_coordData (K := K)
  suffices hz : ∀ x : ContH1.H1 ((rhoK K j).quotientToInvariants (HK K)), x = 0 from
    ⟨fun x y => by rw [hz x, hz y]⟩
  intro x
  apply ContH1.inf_injective (rhoK K j) (HK K)
  rw [map_zero]
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change ContH1.inf (rhoK K j) (HK K) (ContH1.mk ((rhoK K j).quotientToInvariants (HK K)) f) = 0
  rw [ContH1.inf_mk]
  set F := ContH1.infCocycles (rhoK K j) (HK K) f with hFdef
  have hFH : ∀ h : K.fixingSubgroup, h ∈ HK K → (F : K.fixingSubgroup → ℂ_[p]) h = 0 :=
    fun h hh => infCocycles_K_of_mem f hh
  have hFval := infCocycles_K_fixed f
  -- `γ ∈ G_K` and the solution `m`
  obtain ⟨γ, hγK, N, hN, u, hu, hγ⟩ := exists_gamma_K K (N0 := 5) (by norm_num)
  have hT := isTateGen_of_chi (by omega) hu hγ
  obtain ⟨hlam1, hlam⟩ := chiPow_props' hN hu hγ hj
  set γK : K.fixingSubgroup := ⟨γ, hγK⟩
  obtain ⟨m, hm, hmeq⟩ := exists_twist_eq_K D hγK hT (by omega) hlam1 hlam
    (fun h hh => hFval γK hh)
  -- the modified cocycle
  set F' : K.fixingSubgroup → ℂ_[p] :=
    fun g => (F : K.fixingSubgroup → ℂ_[p]) g - (rhoK K j g m - m) with hF'
  have hF'c : F' ∈ ContH1.cocycles (rhoK K j) := by
    refine ⟨F.2.1.sub (((continuous_cpTwistRepQ_apply j m).comp continuous_subtype_val).sub
      continuous_const), fun g h => ?_⟩
    simp only [hF', F.2.2 g h, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hF'γ : F' γK = 0 := by
    simp only [hF']
    change _ - (cpTwistRepQ j γ m - m) = 0
    rw [cpTwistRepQ_apply, hmeq, sub_self]
  have hF'H : ∀ h : K.fixingSubgroup, h ∈ HK K → F' h = 0 := by
    intro h hh
    simp only [hF']
    rw [hFH h hh]
    change 0 - (cpTwistRepQ j (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) m - m) = 0
    rw [cpTwistRepQ_of_mem_HK j ((mem_HK_iff K).mp hh), hm _ ((mem_HK_iff K).mp hh)]
    simp
  have hpow : ∀ k : ℕ, F' (γK ^ k) = 0 := by
    intro k
    induction k with
    | zero => exact ContH1.cocycle_one _ hF'c
    | succ k ih => rw [pow_succ, hF'c.2, ih, hF'γ, map_zero, add_zero]
  have hGN := vanish_of_vanish_pow_K (K := K) (j := j) (γ := γK) (N := N) (by omega) hu hγ
    hF'c hF'H hpow
  haveI := fixingSubgroup_cycField_subgroupOf_finiteIndex (K := K) (p := p) N
  have hidx : (((cycField p N).fixingSubgroup.subgroupOf K.fixingSubgroup).index : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Subgroup.FiniteIndex.index_ne_zero)
  have h0 := ContH1.mk_eq_zero_of_vanish (rhoK K j) _ hidx ⟨F', hF'c⟩
    (fun s hs => hGN s (Subgroup.mem_subgroupOf.mp hs))
  have hcob : ContH1.mk (rhoK K j) (F - ⟨F', hF'c⟩) = 0 := by
    rw [ContH1.mk_eq_zero_iff]
    refine ⟨m, fun g => ?_⟩
    change (F : K.fixingSubgroup → ℂ_[p]) g - F' g = rhoK K j g m - m
    simp only [hF']
    abel
  rw [map_sub, h0, sub_zero] at hcob
  exact hcob

end Main

end PadicHodge
