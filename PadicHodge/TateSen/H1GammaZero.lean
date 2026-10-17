/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.TateSen.H1GammaMain
import PadicHodge.Cyclotomic.Decomp
import PadicHodge.Cyclotomic.LogChi

/-!
# `H¹(Γ, \hat{ℚ_p(μ_{p^∞})}) ≅ ℚ_p`

Let `G = Gal(ℚ̄_p/ℚ_p)`, `H = Gal(ℚ̄_p/ℚ_p(μ_{p^∞}))` and `Γ = G/H`. The continuous cohomology
`H¹(Γ, ℂ_p^H)` is one-dimensional over `ℚ_p`, spanned by the class of `log χ`
(`H1QuotientZeroEquiv : ℚ_p ≃ₗ[ℚ_p] H¹(Γ, ℂ_p^H)`, `a ↦ a [log χ]`). By Ax–Sen–Tate `ℂ_p^H` is
the completion of `ℚ_p(μ_{p^∞})`. ([BC, §14.3]; this is the `Γ`-part of Tate's
`H¹(G_K, ℂ_p) ≅ K`.)

Proof. *Injectivity*: if `a log χ = γ m - m` then `γ m - m ∈ ℚ_p`, which forces it to vanish
(`eq_zero_of_autCp_sub_eq`, normalised traces), and `log χ(γ) ≠ 0`. *Surjectivity*: for a
cocycle `F` (inflated to `G`) write `F(γ) = γ m - m + r` with `r ∈ ℚ_p(μ_{p^5})`
(`exists_decomp`); the modified cocycle `F' = F - ∂m` satisfies `F'(γ) = r`, and since `Γ` is
abelian, `(γ - 1) F'(g) = g r - r` for all `g`, so `g r = r`, i.e. `r = b ∈ ℚ_p`. Then
`F' - (b / log χ(γ)) log χ` vanishes on `H` and on all `γ^k`, hence on
`Gal(ℚ̄_p/ℚ_p(μ_{p^5}))` (`vanish_of_vanish_pow`), and is a coboundary by averaging.
-/

noncomputable section

open IntermediateField Topology

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem cpTwistRepQ_zero_apply (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    cpTwistRepQ (p := p) 0 σ x = autCp σ x := by
  rw [cpTwistRepQ_apply, chiPow_apply, zpow_zero, Units.val_one, PadicInt.coe_one, one_smul]

theorem mem_H_of_chi_eq_one {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (h : chi σ = 1) :
    σ ∈ (cycFieldInf p).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨k, hk⟩ := mem_cycFieldInf.mp hx
  have hσ := mem_of_dvd_chi_sub_one (p := p) (N := max k 1) (le_max_right _ _)
    (by rw [h, Units.val_one, sub_self]; exact dvd_zero _)
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x
    (cycField_mono (le_max_left _ _) hk)

theorem commutator_mem_H (g γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    γ⁻¹ * g⁻¹ * γ * g ∈ (cycFieldInf p).fixingSubgroup := by
  refine mem_H_of_chi_eq_one ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (chi γ)⁻¹ (chi g)⁻¹]
  group

theorem coe_one_cp : ((1 : PadicAlgCl p) : ℂ_[p]) = 1 := by
  rw [PadicComplex.coe_eq, map_one]

theorem autCp_one_smul (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (a : ℚ_[p]) :
    autCp σ (a • (1 : ℂ_[p])) = a • (1 : ℂ_[p]) := by
  rw [autCp_smul, map_one]

/-- `1 ∈ ℂ_p^H`. -/
def oneInv : Representation.invariants
    ((cpTwistRepQ (p := p) 0).comp (cycFieldInf p).fixingSubgroup.subtype) :=
  ⟨1, fun h => by
    change cpTwistRepQ 0 (h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) 1 = 1
    rw [cpTwistRepQ_zero_apply, map_one]⟩

/-- `log χ` on `Γ = G/H`. -/
def logChiQ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ (cycFieldInf p).fixingSubgroup →*
    Multiplicative ℚ_[p] :=
  QuotientGroup.lift _ (logChiHom (p := p)) fun h hh => by
    change logChiHom h = 1
    rw [← ofAdd_logChi, logChi_eq_zero_of_chi_eq_one (chi_eq_one_of_mem_H hh), ofAdd_zero]

theorem logChiQ_mk (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    (logChiQ (p := p) (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ _)).toAdd = logChi g := rfl

/-- The cocycle `log χ : Γ → ℚ_p ⊆ ℂ_p^H`. -/
def logChiCocycle : ContH1.cocycles ((cpTwistRepQ (p := p) 0).quotientToInvariants
    (cycFieldInf p).fixingSubgroup) :=
  ⟨fun x => (logChiQ x).toAdd • oneInv, by
    refine ⟨?_, fun x y => ?_⟩
    · refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
      exact (continuous_logChi (p := p)).smul continuous_const
    · induction x using QuotientGroup.induction_on with | H g => ?_
      induction y using QuotientGroup.induction_on with | H h => ?_
      rw [← QuotientGroup.mk_mul]
      refine Subtype.ext ?_
      change logChi (g * h) • (1 : ℂ_[p]) =
        logChi g • (1 : ℂ_[p]) + cpTwistRepQ 0 g (logChi h • (1 : ℂ_[p]))
      rw [cpTwistRepQ_zero_apply, autCp_one_smul, logChi_mul, add_smul]⟩

variable (p) in
/-- `Γ = G/H` acting on `ℂ_p^H`. -/
abbrev rhoGamma0 := (cpTwistRepQ (p := p) 0).quotientToInvariants (cycFieldInf p).fixingSubgroup

/-- The map `a ↦ a [log χ]`. -/
def logChiClass : ℚ_[p] →ₗ[ℚ_[p]] ContH1.H1 ((cpTwistRepQ (p := p) 0).quotientToInvariants
    (cycFieldInf p).fixingSubgroup) :=
  LinearMap.toSpanSingleton ℚ_[p] _ (ContH1.mk (rhoGamma0 p) logChiCocycle)

theorem logChiClass_injective : Function.Injective (logChiClass (p := p)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [logChiClass, LinearMap.toSpanSingleton_apply, ← map_smul, ContH1.mk_eq_zero_iff] at ha
  obtain ⟨m, hm⟩ := ha
  obtain ⟨γ, u, hu, hγ⟩ := exists_chi_eq (p := p) 5 (by norm_num)
  have hT := isTateGen_of_chi (by norm_num) hu hγ
  have h1 := congrArg Subtype.val (hm (γ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ _))
  change a • (logChi γ • (1 : ℂ_[p])) = cpTwistRepQ 0 γ (m : ℂ_[p]) - m at h1
  rw [cpTwistRepQ_zero_apply, smul_smul] at h1
  have hmcl : (m : ℂ_[p]) ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) := by
    refine mem_closure_of_H_fixed fun h hh => ?_
    rw [← cpTwistRepQ_zero_apply]
    exact m.2 ⟨h, hh⟩
  have hr : (a * logChi γ) • (1 : PadicAlgCl p) ∈ cycField p 5 :=
    IntermediateField.smul_mem _ (one_mem _)
  have h0 := eq_zero_of_autCp_sub_eq hT (by norm_num) hmcl hr
    (by rw [coe_smul_cp, coe_one_cp, h1])
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · rcases mul_eq_zero.mp h0 with h0 | h0
    · exact h0
    · exact absurd h0 (logChi_ne_zero (by norm_num) hu hγ)
  · exact absurd h0 one_ne_zero

/-- **Key step**: a continuous cocycle `F : G → ℂ_p` vanishing on `H` with values in the
closure of `ℚ_p(μ_{p^∞})` is `s log χ` up to a coboundary. -/
theorem exists_eq_logChi_add_coboundary {F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p]}
    (hFc : F ∈ ContH1.cocycles (cpTwistRepQ (p := p) 0))
    (hFH : ∀ h ∈ (cycFieldInf p).fixingSubgroup, F h = 0)
    (hFval : ∀ g, F g ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p])) :
    ∃ s : ℚ_[p], ∃ m : ℂ_[p], ∀ g, F g - (s * logChi g) • (1 : ℂ_[p]) = autCp g m - m := by
  have hFmul : ∀ g h, F (g * h) = F g + autCp g (F h) := fun g h => by
    rw [hFc.2, cpTwistRepQ_zero_apply]
  -- a Tate generator and the decomposition of `F(γ)`
  obtain ⟨γ, u, hu, hγ⟩ := exists_chi_eq (p := p) 5 (by norm_num)
  have hT := isTateGen_of_chi (by norm_num) hu hγ
  obtain ⟨m, hm, r, hr, hmr⟩ := exists_decomp hT (by norm_num) (hFval γ)
  -- `F' = F - ∂m`
  obtain ⟨F', hF'⟩ : ∃ F' : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p],
      ∀ g, F' g = F g - (autCp g m - m) := ⟨_, fun _ => rfl⟩
  have hF'mul : ∀ g h, F' (g * h) = F' g + autCp g (F' h) := fun g h => by
    rw [hF', hF', hF', hFmul, map_mul,
      show (autCp g * autCp h) m = autCp g (autCp h m) from rfl, map_sub, map_sub]
    abel
  have hF'cont : Continuous F' := by
    rw [show F' = fun g => F g - (autCp g m - m) from funext hF']
    exact hFc.1.sub ((continuous_autCp_apply m).sub continuous_const)
  have hF'c : F' ∈ ContH1.cocycles (cpTwistRepQ (p := p) 0) :=
    ⟨hF'cont, fun g h => by rw [hF'mul, cpTwistRepQ_zero_apply]⟩
  have hF'γ : F' γ = (r : ℂ_[p]) := by
    rw [hF', ← hmr]; abel
  have hF'H : ∀ h ∈ (cycFieldInf p).fixingSubgroup, F' h = 0 := by
    intro h hh
    rw [hF', hFH h hh, autCp_eq_self_of_mem_closure hm hh, sub_self, sub_zero]
  -- `F'` takes values in `ℂ_p^H`
  have hF'cl : ∀ g, F' g ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) := by
    intro g
    refine mem_closure_of_H_fixed fun h hh => ?_
    have hc : g⁻¹ * h * g ∈ (cycFieldInf p).fixingSubgroup := by
      have := Subgroup.Normal.conj_mem (inferInstance : (cycFieldInf p).fixingSubgroup.Normal)
        h hh g⁻¹
      rwa [inv_inv] at this
    have e1 := hF'mul h g
    have e2 := hF'mul g (g⁻¹ * h * g)
    rw [hF'H h hh, zero_add] at e1
    rw [hF'H _ hc, map_zero, add_zero, show g * (g⁻¹ * h * g) = h * g by group] at e2
    rw [← e1, e2]
  -- `r` is fixed by `G`, hence lies in `ℚ_p`
  have hrfix : ∀ g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, g r = r := by
    intro g
    have hcomm : γ * g = g * γ * (γ⁻¹ * g⁻¹ * γ * g) := by group
    have e1 : F' (γ * g) = F' g + autCp g (F' γ) := by
      rw [hcomm, hF'mul, hF'H _ (commutator_mem_H g γ), map_zero, add_zero, hF'mul]
    rw [hF'mul, hF'γ] at e1
    have e2 : autCp γ (F' g) - F' g = ((g r - r : PadicAlgCl p) : ℂ_[p]) := by
      rw [coe_sub_cp, ← autCp_coe]; linear_combination e1
    have hgr : g r - r ∈ cycField p 5 := sub_mem (gal_mem_cycField g hr) hr
    exact sub_eq_zero.mp (eq_zero_of_autCp_sub_eq hT (by norm_num) (hF'cl g) hgr e2)
  obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[p]) r).mpr hrfix
  have hbr : ((r : PadicAlgCl p) : ℂ_[p]) = b • (1 : ℂ_[p]) := by
    rw [← hb, Algebra.algebraMap_eq_smul_one, coe_smul_cp, coe_one_cp]
  -- subtract `s log χ`
  have hlog0 := logChi_ne_zero (by norm_num) hu hγ
  set s := b / logChi γ with hs
  have hF''c : (fun g => F' g - (s * logChi g) • (1 : ℂ_[p])) ∈
      ContH1.cocycles (cpTwistRepQ (p := p) 0) := by
    refine ⟨hF'c.1.sub ((continuous_const.mul continuous_logChi).smul continuous_const),
      fun g h => ?_⟩
    change F' (g * h) - (s * logChi (g * h)) • (1 : ℂ_[p]) =
      (F' g - (s * logChi g) • (1 : ℂ_[p])) + cpTwistRepQ 0 g (F' h - (s * logChi h) • 1)
    rw [hF'mul, cpTwistRepQ_zero_apply, map_sub, autCp_one_smul, logChi_mul, mul_add, add_smul]
    abel
  have hF''γ : F' γ - (s * logChi γ) • (1 : ℂ_[p]) = 0 := by
    rw [hF'γ, hbr, hs, div_mul_cancel₀ _ hlog0, sub_self]
  have hpow : ∀ k : ℕ, F' (γ ^ k) - (s * logChi (γ ^ k)) • (1 : ℂ_[p]) = 0 := by
    intro k
    induction k with
    | zero => exact ContH1.cocycle_one _ hF''c
    | succ k ih =>
      have := hF''c.2 (γ ^ k) γ
      beta_reduce at this
      rw [← pow_succ] at this
      rw [this, ih, hF''γ, map_zero, add_zero]
  have hF''H : ∀ h ∈ (cycFieldInf p).fixingSubgroup,
      F' h - (s * logChi h) • (1 : ℂ_[p]) = 0 := by
    intro h hh
    rw [hF'H h hh, logChi_eq_zero_of_chi_eq_one (chi_eq_one_of_mem_H hh), mul_zero, zero_smul,
      sub_zero]
  have hG5 := vanish_of_vanish_pow hu hγ hF''c hF''H hpow
  haveI := fixingSubgroup_cycField_finiteIndex (p := p) 5
  have hidx : ((cycField p 5).fixingSubgroup.index : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Subgroup.FiniteIndex.index_ne_zero)
  have h0 := ContH1.mk_eq_zero_of_vanish _ _ hidx ⟨_, hF''c⟩ hG5
  rw [ContH1.mk_eq_zero_iff] at h0
  obtain ⟨m', hm'⟩ := h0
  refine ⟨s, m + m', fun g => ?_⟩
  have := hm' g
  simp only [cpTwistRepQ_zero_apply] at this
  rw [map_add]
  change F' g - (s * logChi g) • (1 : ℂ_[p]) = autCp g m' - m' at this
  rw [hF'] at this
  linear_combination this

theorem infCocycles_logChiCocycle (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    (ContH1.infCocycles (cpTwistRepQ (p := p) 0) (cycFieldInf p).fixingSubgroup
      logChiCocycle : _ → ℂ_[p]) g = logChi g • (1 : ℂ_[p]) := rfl

set_option maxHeartbeats 1000000 in
-- unfolding the quotient `H¹` of cocycles with values in `ℂ_p^H` is expensive
theorem logChiClass_surjective : Function.Surjective (logChiClass (p := p)) := by
  intro x
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨s, m, hm⟩ := exists_eq_logChi_add_coboundary
    (ContH1.infCocycles (cpTwistRepQ (p := p) 0) _ f).2
    (fun h hh => infCocycles_twist_of_mem_H f hh) (infCocycles_twist_mem_closure f)
  have hmH : m ∈ Representation.invariants
      ((cpTwistRepQ (p := p) 0).comp (cycFieldInf p).fixingSubgroup.subtype) := by
    rintro ⟨h, hh⟩
    have := hm h
    rw [infCocycles_twist_of_mem_H f hh, logChi_eq_zero_of_chi_eq_one (chi_eq_one_of_mem_H hh),
      mul_zero, zero_smul, sub_zero, eq_comm, sub_eq_zero] at this
    change cpTwistRepQ 0 h m = m
    rw [cpTwistRepQ_zero_apply, this]
  refine ⟨s, ?_⟩
  rw [logChiClass, LinearMap.toSpanSingleton_apply, ← map_smul, ← sub_eq_zero, ← map_sub,
    ContH1.mk_eq_zero_iff]
  refine ⟨-⟨m, hmH⟩, fun x => ?_⟩
  induction x using QuotientGroup.induction_on with | H g => ?_
  apply Subtype.ext
  have := hm g
  change s • (logChi g • (1 : ℂ_[p])) -
    (ContH1.infCocycles (cpTwistRepQ (p := p) 0) _ f : _ → ℂ_[p]) g =
      cpTwistRepQ 0 g (-m) - -m
  rw [cpTwistRepQ_zero_apply, map_neg, smul_smul]
  linear_combination -this

/-- **`H¹(Γ, \hat{ℚ_p(μ_{p^∞})}) ≅ ℚ_p`**: `a ↦ a [log χ]` is an isomorphism
`ℚ_p ≅ H¹(Γ, ℂ_p^H)`, `Γ = Gal(ℚ_p(μ_{p^∞})/ℚ_p)`, `H = Gal(ℚ̄_p/ℚ_p(μ_{p^∞}))`. -/
def H1QuotientZeroEquiv : ℚ_[p] ≃ₗ[ℚ_[p]] ContH1.H1 ((cpTwistRepQ (p := p) 0).quotientToInvariants
    (cycFieldInf p).fixingSubgroup) :=
  LinearEquiv.ofBijective logChiClass ⟨logChiClass_injective, logChiClass_surjective⟩

theorem H1QuotientZeroEquiv_apply (a : ℚ_[p]) :
    H1QuotientZeroEquiv (p := p) a = a • ContH1.mk (rhoGamma0 p) logChiCocycle := rfl

theorem finrank_H1_quotient_zero :
    Module.finrank ℚ_[p] (ContH1.H1 ((cpTwistRepQ (p := p) 0).quotientToInvariants
      (cycFieldInf p).fixingSubgroup)) = 1 := by
  rw [← H1QuotientZeroEquiv.finrank_eq, Module.finrank_self]

end PadicHodge
