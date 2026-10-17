/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Solve
import PadicHodge.TateSen.Invariants
import PadicHodge.Cohomology.ContH1
import PadicHodge.Galois.Continuity
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Multiplicity

/-!
# `H¹(Γ, \hat{ℚ_p(μ_{p^∞})}(j)) = 0` for `j ≠ 0`

Let `G = Gal(ℚ̄_p/ℚ_p)`, `H = Gal(ℚ̄_p/ℚ_p(μ_{p^∞}))` (normal) and `Γ = G/H`. For `j ≠ 0` the
continuous cohomology `H¹(Γ, (ℂ_p(j))^H)` vanishes (`subsingleton_H1_quotient_twist`); by
Ax–Sen–Tate `(ℂ_p(j))^H` is the completion of `ℚ_p(μ_{p^∞})` with `Γ` acting through `χ^j`.
([BC, §14.3]; this is the `Γ`-part of Tate's `H¹(G_K, ℂ_p(j)) = 0`.)

Proof: inflate a cocycle to `G`; it takes values in the completion of `ℚ_p(μ_{p^∞})` and vanishes
on `H`. Modify it by the coboundary of a solution `m` of `χ(γ)^j γ m - m = f(γ)`
(`exists_twist_eq`, Tate's normalised traces) for a Tate generator `γ` at level `5`. The new
cocycle vanishes on all `γ^k`, hence (by the density of `γ^ℕ H` in `Gal(ℚ̄_p/ℚ_p(μ_{p^5}))`,
`exists_pow_dvd_sub`, and compactness of `G`) on `Gal(ℚ̄_p/ℚ_p(μ_{p^5}))`, a subgroup of finite
index; averaging (`ContH1.mk_eq_zero_of_vanish`) shows that it is a coboundary.
-/

noncomputable section

open IntermediateField Topology Pointwise

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Continuity -/

theorem continuous_gal_apply_Qp (x : PadicAlgCl p) :
    Continuous fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p => σ x := by
  have hopen := stabilizer_isOpen_of_isIntegral (K := ℚ_[p]) x
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • ((MulAction.stabilizer (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x : Subgroup _) :
    Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)), ?_,
    hopen.leftCoset σ, ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, AlgEquiv.mul_apply]
  have : τ x = x := hτ
  rw [this]
  exact hσ

theorem continuous_autCp_apply (x : ℂ_[p]) :
    Continuous fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p => autCp σ x := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨y, hy⟩ : ∃ y : PadicAlgCl p, dist x y < ε :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  refine ⟨fun σ => ((σ y : PadicAlgCl p) : ℂ_[p]),
    UniformSpace.Completion.continuous_coe _ |>.comp (continuous_gal_apply_Qp y), fun σ => ?_⟩
  apply hεu
  change dist (autCp σ x) ((σ y : PadicAlgCl p) : ℂ_[p]) < ε
  rw [← autCp_coe, dist_eq_norm, ← map_sub, norm_autCp, ← dist_eq_norm]
  exact hy

theorem continuous_chiPow (j : ℤ) :
    Continuous fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p =>
      ((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p]) := by
  have h := cyclotomicCharacter.continuous p ℚ_[p] (PadicAlgCl p)
  have h1 : Continuous fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p => chi σ ^ j :=
    (continuous_zpow j).comp h
  have hc : Continuous (fun z : ℤ_[p] => (z : ℚ_[p])) :=
    Metric.continuous_iff.mpr fun b ε hε => ⟨ε, hε, fun a h => h⟩
  exact hc.comp (Units.continuous_val.comp h1)

theorem norm_chiPow (j : ℤ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ‖((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  rw [chiPow_apply, PadicInt.padic_norm_e_of_padicInt, ← PadicInt.isUnit_iff]
  exact Units.isUnit _

/-! ### The twisted representation over `ℚ_p` -/

/-- `ℂ_p(j)` as a representation of `Gal(ℚ̄_p/ℚ_p)`: `σ · c = χ(σ)^j σ(c)`. -/
def cpTwistRepQ (j : ℤ) : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ℂ_[p] where
  toFun σ :=
    { toFun := fun x => ((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p]) • autCp σ x
      map_add' := fun x y => by rw [map_add, smul_add]
      map_smul' := fun c x => by rw [autCp_smul, smul_comm]; rfl }
  map_one' := by ext x; simp
  map_mul' σ τ := by
    ext x
    change ((chiPow j (σ * τ) : ℚ_[p]ˣ) : ℚ_[p]) • autCp (σ * τ) x =
      ((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p]) • autCp σ (((chiPow j τ : ℚ_[p]ˣ) : ℚ_[p]) • autCp τ x)
    rw [map_mul, map_mul, Units.val_mul, autCp_smul, smul_smul]
    rfl

theorem cpTwistRepQ_apply (j : ℤ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    cpTwistRepQ j σ x = ((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p]) • autCp σ x := rfl

theorem continuous_cpTwistRepQ_apply (j : ℤ) (x : ℂ_[p]) :
    Continuous fun σ => cpTwistRepQ (p := p) j σ x :=
  (continuous_chiPow j).smul (continuous_autCp_apply x)

theorem norm_cpTwistRepQ (j : ℤ) (σ) (x : ℂ_[p]) : ‖cpTwistRepQ (p := p) j σ x‖ = ‖x‖ := by
  rw [cpTwistRepQ_apply, norm_smul, norm_chiPow, norm_autCp, one_mul]

/-! ### The subgroup `H = Gal(ℚ̄_p/ℚ_p(μ_{p^∞}))` -/

instance normal_fixingSubgroup_cycFieldInf : (cycFieldInf p).fixingSubgroup.Normal := by
  constructor
  intro h hh g
  rw [IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
  intro x hx
  obtain ⟨k, hk⟩ := mem_cycFieldInf.mp hx
  have h1 : g⁻¹ x ∈ cycFieldInf p := mem_cycFieldInf.mpr ⟨k, gal_mem_cycField _ hk⟩
  simp only [AlgEquiv.mul_apply]
  rw [hh _ h1]
  exact AlgEquiv.apply_symm_apply g x

theorem chi_eq_one_of_mem_H {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hh : h ∈ (cycFieldInf p).fixingSubgroup) : chi h = 1 := by
  refine chi_eq_one_of_fix fun k t ht => ?_
  rw [IntermediateField.mem_fixingSubgroup_iff] at hh
  exact hh t (mem_cycFieldInf.mpr ⟨k, pow_mem_cycField ht⟩)

theorem cpTwistRepQ_of_mem_H (j : ℤ) {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hh : h ∈ (cycFieldInf p).fixingSubgroup) (x : ℂ_[p]) : cpTwistRepQ j h x = autCp h x := by
  rw [cpTwistRepQ_apply, chiPow_apply, chi_eq_one_of_mem_H hh, one_zpow, Units.val_one,
    PadicInt.coe_one, one_smul]

/-- Elements of `ℂ_p` fixed by `H` lie in the closure of `ℚ_p(μ_{p^∞})` (Ax–Sen–Tate). -/
theorem mem_closure_of_H_fixed {x : ℂ_[p]}
    (hx : ∀ h ∈ (cycFieldInf p).fixingSubgroup, autCp h x = x) :
    x ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) := by
  refine (galCp_eq_self_iff_mem_closure x).mp fun σ => ?_
  have hσ : σ.restrictScalars ℚ_[p] ∈ (cycFieldInf p).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact σ.commutes ⟨y, hy⟩
  exact hx _ hσ

theorem autCp_eq_self_of_mem_closure {x : ℂ_[p]}
    (hx : x ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]))
    {h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hh : h ∈ (cycFieldInf p).fixingSubgroup) :
    autCp h x = x := by
  have e := galCp_eq_self_of_mem_closure hx ((fixingSubgroupEquiv (cycFieldInf p)) ⟨h, hh⟩)
  have e2 : ((fixingSubgroupEquiv (cycFieldInf p)) ⟨h, hh⟩).restrictScalars ℚ_[p] = h := by
    ext; rfl
  rwa [galCp_eq_autCp, e2] at e

/-! ### Density of `γ^ℕ H` -/

theorem isUnit_one_add_p_pow {n : ℕ} (hn : 1 ≤ n) (u : ℤ_[p]) :
    IsUnit (1 + (p : ℤ_[p]) ^ n * u) := by
  refine isUnit_add_of_norm_lt isUnit_one ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ', mul_assoc]
  exact norm_p_mul_lt_one _

/-- If `s ≡ 1 (mod p^n)` and `c = 1 + p^n u` (`n ≥ 2`, `u` a unit), then for every `N ≥ n`
some power `c^k` (`k ∈ ℕ`) is `≡ s (mod p^N)`. -/
theorem exists_pow_dvd_sub {n : ℕ} (hn : 2 ≤ n) {u : ℤ_[p]} (hu : IsUnit u) {s : ℤ_[p]}
    (hs : (p : ℤ_[p]) ^ n ∣ s - 1) {N : ℕ} (hN : n ≤ N) :
    ∃ k : ℕ, (p : ℤ_[p]) ^ N ∣ s - (1 + (p : ℤ_[p]) ^ n * u) ^ k := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨0, by simpa using hs⟩
  | succ N hnN ih =>
    obtain ⟨k, t, ht⟩ := ih
    set c := 1 + (p : ℤ_[p]) ^ n * u with hc
    obtain ⟨u', hu', he⟩ := one_add_pow_p_pow hn hu (N - n)
    rw [show n + (N - n) = N by omega] at he
    have hcu : IsUnit c := isUnit_one_add_p_pow (by omega) u
    set w := c ^ k * u' with hw
    have hwu : IsUnit w := (hcu.pow k).mul hu'
    set a : ℕ := (PadicInt.toZModPow 1 (t * ((hwu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))).val with ha
    have hpa : (p : ℤ_[p]) ∣ t - a * w := by
      have htw : t * ((hwu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * w = t := by
        rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
      have h0 : t - a * w ∈ RingHom.ker (PadicInt.toZModPow (p := p) 1) := by
        rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, ha, ZMod.natCast_val, ZMod.cast_id',
          id, ← map_mul, htw, sub_self]
      rwa [PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one] at h0
    obtain ⟨q, hq⟩ := hpa
    -- `(1 + x)^a - 1 - a x` is divisible by `x^2`
    set x := (p : ℤ_[p]) ^ N * u' with hx
    obtain ⟨r, hr⟩ := sq_dvd_add_pow_sub_sub x (1 : ℤ_[p]) a
    simp only [one_pow, one_mul] at hr
    refine ⟨k + a * p ^ (N - n), (p : ℤ_[p]) ^ N * 0 + (q - c ^ k * (p : ℤ_[p]) ^ (N - 1) *
      u' ^ 2 * r), ?_⟩
    have he' : c ^ (p ^ (N - n)) = 1 + x := by rw [hc, hx]; exact he
    have hck : c ^ (k + a * p ^ (N - n)) = c ^ k * (1 + x) ^ a := by
      rw [pow_add, mul_comm a, pow_mul, he']
    have h1 : (1 + x) ^ a = 1 + x * a + x ^ 2 * r := by
      rw [add_comm (1 : ℤ_[p]) x]
      linear_combination hr
    rw [hck, h1]
    have hN1 : (p : ℤ_[p]) ^ (2 * N) = (p : ℤ_[p]) ^ (N + 1) * (p : ℤ_[p]) ^ (N - 1) := by
      rw [← pow_add]; congr 1; omega
    have e1 : s - c ^ k * (1 + x * a + x ^ 2 * r) =
        (s - c ^ k) - (p : ℤ_[p]) ^ N * (a * w) - c ^ k * x ^ 2 * r := by
      rw [hx, hw]; ring
    rw [e1, ht]
    have e2 : x ^ 2 = (p : ℤ_[p]) ^ (2 * N) * u' ^ 2 := by rw [hx]; ring
    rw [e2, hN1]
    have e3 : t = a * w + p * q := by rw [← hq]; ring
    rw [e3]
    ring

/-- `σ` fixes `ℚ_p(μ_{p^n})` iff `p^n ∣ χ(σ) - 1` (one direction). -/
theorem dvd_chi_sub_one_of_mem {n : ℕ} {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hσ : σ ∈ (cycField p n).fixingSubgroup) :
    (p : ℤ_[p]) ^ n ∣ ((chi σ : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) n
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have hfixζ : σ ζ = ζ ^ 1 := by
    rw [pow_one]; exact hσ ζ (pow_mem_cycField hζ.pow_eq_one)
  have h := toZModPow_chi_of_apply hζ hfixζ
  have h0 : ((chi σ : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := p) n) := by
    rw [RingHom.mem_ker, map_sub, h, map_one, Nat.cast_one, sub_self]
  rwa [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h0

theorem mem_of_dvd_chi_sub_one {N : ℕ} (hN : 1 ≤ N) {τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hτ : (p : ℤ_[p]) ^ N ∣ ((chi τ : ℤ_[p]ˣ) : ℤ_[p]) - 1) :
    τ ∈ (cycField p N).fixingSubgroup := by
  have h1 : PadicInt.toZModPow N ((chi τ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    have : ((chi τ : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := p) N) := by
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; exact hτ
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact this
  have hfix : ∀ t : PadicAlgCl p, t ^ (p ^ N) = 1 → τ t = t := by
    intro t ht
    rw [chi_spec τ ht, h1]
    haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
    rw [ZMod.val_one, pow_one]
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) N
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  rw [cycField_eq hζ] at hy
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  rw [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨f, rfl⟩ := hy
  change τ (Polynomial.aeval ζ f) = Polynomial.aeval ζ f
  rw [← Polynomial.aeval_algHom_apply]
  rw [hfix ζ hζ.pow_eq_one]

end PadicHodge
