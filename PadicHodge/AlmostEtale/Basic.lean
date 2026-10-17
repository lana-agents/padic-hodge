/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Tower
import Mathlib.FieldTheory.NormalizedTrace

/-!
# Integral elements, polynomials with integral coefficients, normalised traces

Basic tools for the almost-étale milestone (PH1.AE), all inside `ℚ̄_p = PadicAlgCl p`:

* `ballK p`: the closed unit ball of `ℚ̄_p`, a subring; `OK F = F ∩ ballK p`, the ring of
  integers of an intermediate field `F`;
* `polyOver S`: polynomials over `ℚ̄_p` with coefficients in a subring `S`, closed under
  derivatives, composition, and division by monic polynomials (`divByMonic_mem`);
* `adj S z`: the ring `S[z]`;
* `mp F z`: the minimal polynomial of `z` over `F`, viewed in `ℚ̄_p[X]`; its roots are
  conjugates of `z`, hence have the same norm (`norm_eq_of_isRoot_mp`), so for `‖z‖ ≤ 1` it has
  integral coefficients (`mp_mem_polyOver`); a polynomial in `O_F[X]` vanishing at `z` is
  divisible by `mp F z` in `O_F[X]` (`exists_eq_mp_mul`);
* `nt F`: Mathlib's normalised trace `ℚ̄_p → F` (`Algebra.normalizedTrace`), viewed as a map to
  `ℚ̄_p`; transitivity (`nt_nt`); the trace bound `‖[N : F] nt_F(y)‖ ≤ ‖y‖` for `y ∈ N`
  (`norm_deg_mul_nt_le`).
-/

noncomputable section

open Polynomial IntermediateField Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

/-! ### The unit ball and rings of integers -/

variable (p) in
/-- The closed unit ball of `ℚ̄_p`, a subring. -/
def ballK : Subring (PadicAlgCl p) where
  carrier := {y | ‖y‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem mem_ballK {y : PadicAlgCl p} : y ∈ ballK p ↔ ‖y‖ ≤ 1 := Iff.rfl

/-- The ring of integers `O_F = F ∩ {‖y‖ ≤ 1}` of an intermediate field. -/
def OK (F : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subring (PadicAlgCl p) :=
  F.toSubfield.toSubring ⊓ ballK p

theorem mem_OK {F : IntermediateField ℚ_[p] (PadicAlgCl p)} {y : PadicAlgCl p} :
    y ∈ OK F ↔ y ∈ F ∧ ‖y‖ ≤ 1 := Iff.rfl

theorem OK_le_ballK (F : IntermediateField ℚ_[p] (PadicAlgCl p)) : OK F ≤ ballK p :=
  inf_le_right

theorem OK_mono {F F' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : F ≤ F') : OK F ≤ OK F' :=
  fun _ hy => ⟨h hy.1, hy.2⟩

/-! ### Polynomials with coefficients in a subring -/

/-- Polynomials over `ℚ̄_p` with all coefficients in `S`. -/
def polyOver (S : Subring (PadicAlgCl p)) : Subring (PadicAlgCl p)[X] :=
  Polynomial.liftsRing S.subtype

theorem mem_polyOver {S : Subring (PadicAlgCl p)} {q : (PadicAlgCl p)[X]} :
    q ∈ polyOver S ↔ ∀ n, q.coeff n ∈ S := by
  rw [polyOver, ← lifts_iff_liftsRing, lifts_iff_coeff_lifts]
  simp

theorem polyOver_mono {S T : Subring (PadicAlgCl p)} (h : S ≤ T) : polyOver S ≤ polyOver T :=
  fun _ hq => mem_polyOver.mpr fun n => h (mem_polyOver.mp hq n)

theorem C_mem_polyOver {S : Subring (PadicAlgCl p)} {a : PadicAlgCl p} (ha : a ∈ S) :
    C a ∈ polyOver S := by
  rw [mem_polyOver]
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem X_mem_polyOver (S : Subring (PadicAlgCl p)) : (X : (PadicAlgCl p)[X]) ∈ polyOver S := by
  rw [mem_polyOver]
  intro n
  rw [coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem derivative_mem_polyOver {S : Subring (PadicAlgCl p)} {q : (PadicAlgCl p)[X]}
    (hq : q ∈ polyOver S) : derivative q ∈ polyOver S := by
  rw [mem_polyOver] at hq ⊢
  intro n
  rw [coeff_derivative]
  exact mul_mem (hq _) (by exact_mod_cast natCast_mem S (n + 1))

theorem exists_lift {S : Subring (PadicAlgCl p)} {q : (PadicAlgCl p)[X]} (hq : q ∈ polyOver S) :
    ∃ q₀ : S[X], q₀.map S.subtype = q := by
  rw [polyOver, ← lifts_iff_liftsRing] at hq
  exact hq

theorem map_mem_polyOver {S : Subring (PadicAlgCl p)} (q₀ : S[X]) :
    q₀.map S.subtype ∈ polyOver S := by
  rw [polyOver, ← lifts_iff_liftsRing]
  exact ⟨q₀, rfl⟩

theorem comp_mem_polyOver {S : Subring (PadicAlgCl p)} {q r : (PadicAlgCl p)[X]}
    (hq : q ∈ polyOver S) (hr : r ∈ polyOver S) : q.comp r ∈ polyOver S := by
  obtain ⟨q₀, rfl⟩ := exists_lift hq
  obtain ⟨r₀, rfl⟩ := exists_lift hr
  rw [← Polynomial.map_comp]
  exact map_mem_polyOver _

theorem divByMonic_mem_polyOver {S : Subring (PadicAlgCl p)} {q g : (PadicAlgCl p)[X]}
    (hq : q ∈ polyOver S) (hg : g ∈ polyOver S) (hgm : g.Monic) :
    q /ₘ g ∈ polyOver S ∧ q %ₘ g ∈ polyOver S := by
  obtain ⟨q₀, rfl⟩ := exists_lift hq
  have hg' : g ∈ lifts S.subtype := by rw [lifts_iff_liftsRing]; exact hg
  obtain ⟨g₀, hg₀, -, hg₀m⟩ := lifts_and_degree_eq_and_monic hg' hgm
  subst hg₀
  rw [← map_divByMonic _ hg₀m, ← map_modByMonic _ hg₀m]
  exact ⟨map_mem_polyOver _, map_mem_polyOver _⟩

theorem eval_mem {S : Subring (PadicAlgCl p)} {q : (PadicAlgCl p)[X]} (hq : q ∈ polyOver S)
    {z : PadicAlgCl p} (hz : z ∈ S) : q.eval z ∈ S := by
  rw [eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (mem_polyOver.mp hq i) (pow_mem hz _)

/-! ### The rings `S[z]` -/

/-- `S[z] = {q(z) : q ∈ S[X]}`. -/
def adj (S : Subring (PadicAlgCl p)) (z : PadicAlgCl p) : Subring (PadicAlgCl p) :=
  (polyOver S).map (evalRingHom z)

theorem mem_adj {S : Subring (PadicAlgCl p)} {z y : PadicAlgCl p} :
    y ∈ adj S z ↔ ∃ q ∈ polyOver S, q.eval z = y := by
  simp [adj]

theorem eval_mem_adj {S : Subring (PadicAlgCl p)} {q : (PadicAlgCl p)[X]} (hq : q ∈ polyOver S)
    (z : PadicAlgCl p) : q.eval z ∈ adj S z :=
  mem_adj.mpr ⟨q, hq, rfl⟩

theorem self_mem_adj (S : Subring (PadicAlgCl p)) (z : PadicAlgCl p) : z ∈ adj S z :=
  mem_adj.mpr ⟨X, X_mem_polyOver S, eval_X⟩

theorem le_adj (S : Subring (PadicAlgCl p)) (z : PadicAlgCl p) : S ≤ adj S z :=
  fun a ha => mem_adj.mpr ⟨C a, C_mem_polyOver ha, eval_C⟩

theorem adj_mono {S T : Subring (PadicAlgCl p)} (h : S ≤ T) (z : PadicAlgCl p) :
    adj S z ≤ adj T z := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := mem_adj.mp hy
  exact mem_adj.mpr ⟨q, polyOver_mono h hq, rfl⟩

theorem adj_le_ballK {S : Subring (PadicAlgCl p)} (hS : S ≤ ballK p) {z : PadicAlgCl p}
    (hz : ‖z‖ ≤ 1) : adj S z ≤ ballK p := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := mem_adj.mp hy
  exact eval_mem (polyOver_mono hS hq) hz

theorem norm_le_one_of_mem_adj {F : IntermediateField ℚ_[p] (PadicAlgCl p)} {z y : PadicAlgCl p}
    (hz : ‖z‖ ≤ 1) (hy : y ∈ adj (OK F) z) : ‖y‖ ≤ 1 :=
  adj_le_ballK (OK_le_ballK F) hz hy

/-- `S[z] ⊆ T` when `S ⊆ T` and `z ∈ T`. -/
theorem adj_le {S T : Subring (PadicAlgCl p)} (h : S ≤ T) {z : PadicAlgCl p} (hz : z ∈ T) :
    adj S z ≤ T := by
  intro y hy
  obtain ⟨q, hq, rfl⟩ := mem_adj.mp hy
  exact eval_mem (polyOver_mono h hq) hz

/-- Evaluating a polynomial over `S[z]` at an element of `S[z]` stays in `S[z]`. -/
theorem eval_mem_adj_of_mem {S : Subring (PadicAlgCl p)} {z x : PadicAlgCl p}
    (hx : x ∈ adj S z) {q : (PadicAlgCl p)[X]} (hq : q ∈ polyOver S) : q.eval x ∈ adj S z :=
  eval_mem (polyOver_mono (le_adj S z) hq) hx

/-! ### Minimal polynomials -/

/-- The minimal polynomial of `z` over `F`, as a polynomial over `ℚ̄_p`. -/
def mp (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (z : PadicAlgCl p) : (PadicAlgCl p)[X] :=
  (minpoly F z).map (algebraMap F (PadicAlgCl p))

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isIntegral_over (z : PadicAlgCl p) : IsIntegral F z :=
  (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) z).tower_top

theorem mp_monic (z : PadicAlgCl p) : (mp F z).Monic :=
  (minpoly.monic (isIntegral_over F z)).map _

theorem eval_mp (z : PadicAlgCl p) : (mp F z).eval z = 0 := by
  rw [mp, eval_map_algebraMap]
  exact minpoly.aeval F z

theorem natDegree_mp (z : PadicAlgCl p) : (mp F z).natDegree = (minpoly F z).natDegree :=
  natDegree_map _

theorem mp_ne_zero (z : PadicAlgCl p) : mp F z ≠ 0 := (mp_monic F z).ne_zero

theorem coeff_mp_mem (z : PadicAlgCl p) (n : ℕ) : (mp F z).coeff n ∈ F := by
  rw [mp, coeff_map]
  exact ((minpoly F z).coeff n).2

/-- Roots of `mp F z` are conjugates of `z` over `ℚ_p`, hence have the same norm. -/
theorem norm_eq_of_isRoot_mp {z w : PadicAlgCl p} (hw : (mp F z).IsRoot w) : ‖w‖ = ‖z‖ := by
  have hz : IsIntegral ℚ_[p] z := Algebra.IsIntegral.isIntegral z
  -- `w` is a root of `minpoly ℚ_p z`
  have h1 : minpoly F z ∣ (minpoly ℚ_[p] z).map (algebraMap ℚ_[p] F) :=
    minpoly.dvd_map_of_isScalarTower ℚ_[p] F z
  have h2 : aeval w (minpoly ℚ_[p] z) = 0 := by
    obtain ⟨r, hr⟩ := h1
    have := congrArg (fun q => q.map (algebraMap F (PadicAlgCl p))) hr
    simp only [Polynomial.map_map, Polynomial.map_mul] at this
    rw [← IsScalarTower.algebraMap_eq] at this
    rw [aeval_def, eval₂_eq_eval_map, this, eval_mul]
    rw [IsRoot, mp] at hw
    rw [hw, zero_mul]
  have h3 : minpoly ℚ_[p] z = minpoly ℚ_[p] w :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hz) h2 (minpoly.monic hz))
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, h3]

/-- The minimal polynomial is the product of `X - w` over its roots in `ℚ̄_p`. -/
theorem mp_eq_prod_roots (z : PadicAlgCl p) :
    mp F z = ((mp F z).roots.map fun w => X - C w).prod :=
  Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _) (mp_monic F z)

/-- For `‖z‖ ≤ 1` the minimal polynomial of `z` over `F` has coefficients in `O_F`. -/
theorem mp_mem_polyOver {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) : mp F z ∈ polyOver (OK F) := by
  have hball : mp F z ∈ polyOver (ballK p) := by
    rw [mp_eq_prod_roots]
    refine multiset_prod_mem _ fun q hq => ?_
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hq
    have hw' : (mp F z).IsRoot w := (mem_roots (mp_ne_zero F z)).mp hw
    refine sub_mem (X_mem_polyOver _) (C_mem_polyOver ?_)
    rw [mem_ballK, norm_eq_of_isRoot_mp F hw']
    exact hz
  rw [mem_polyOver] at hball ⊢
  exact fun n => ⟨coeff_mp_mem F z n, hball n⟩

/-- A polynomial with coefficients in `F` vanishing at `z` and of degree less than that of the
minimal polynomial is zero. -/
theorem eq_zero_of_eval_eq_zero {z : PadicAlgCl p} {r : (PadicAlgCl p)[X]}
    (hr : ∀ n, r.coeff n ∈ F) (hrz : r.eval z = 0) (hdeg : r.degree < (mp F z).degree) :
    r = 0 := by
  have hl : r ∈ lifts (algebraMap F (PadicAlgCl p)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨r.coeff n, hr n⟩, rfl⟩
  obtain ⟨r₀, hr₀e⟩ := hl
  rw [coe_mapRingHom] at hr₀e
  subst hr₀e
  have h0 : aeval z r₀ = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  by_contra hne
  have hr₀ : r₀ ≠ 0 := fun h => hne (by rw [h, Polynomial.map_zero])
  have := minpoly.degree_le_of_ne_zero F z hr₀ h0
  rw [mp, degree_map, degree_map] at hdeg
  exact absurd hdeg (not_lt.mpr this)

/-- **Division by the minimal polynomial in `O_F[X]`.** -/
theorem exists_eq_mp_mul {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) {q : (PadicAlgCl p)[X]}
    (hq : q ∈ polyOver (OK F)) (hqz : q.eval z = 0) :
    ∃ k ∈ polyOver (OK F), q = mp F z * k := by
  have hg := mp_mem_polyOver F hz
  have hm := mp_monic F z
  obtain ⟨hdiv, hmod⟩ := divByMonic_mem_polyOver hq hg hm
  refine ⟨q /ₘ mp F z, hdiv, ?_⟩
  have hr : q %ₘ mp F z = 0 := by
    refine eq_zero_of_eval_eq_zero F (fun n => (mem_polyOver.mp hmod n).1) ?_
      (degree_modByMonic_lt _ hm)
    have h := modByMonic_add_div q (mp F z)
    have := congrArg (eval z) h
    rw [eval_add, eval_mul, eval_mp, zero_mul, add_zero, hqz] at this
    exact this
  have h := modByMonic_add_div q (mp F z)
  rw [hr, zero_add] at h
  exact h.symm

/-! ### Normalised traces -/

/-- The normalised trace `ℚ̄_p → F`, `y ↦ Tr_{F(y)/F}(y) / [F(y) : F]`, as a map to `ℚ̄_p`. -/
def nt (y : PadicAlgCl p) : PadicAlgCl p :=
  (Algebra.normalizedTrace F (PadicAlgCl p) y : PadicAlgCl p)

theorem nt_mem (y : PadicAlgCl p) : nt F y ∈ F :=
  (Algebra.normalizedTrace F (PadicAlgCl p) y).2

theorem nt_add (y y' : PadicAlgCl p) : nt F (y + y') = nt F y + nt F y' := by
  simp [nt]

theorem nt_sub (y y' : PadicAlgCl p) : nt F (y - y') = nt F y - nt F y' := by
  simp [nt]

theorem nt_mul_left {c : PadicAlgCl p} (hc : c ∈ F) (y : PadicAlgCl p) :
    nt F (c * y) = c * nt F y := by
  have := (Algebra.normalizedTrace F (PadicAlgCl p)).map_smul (⟨c, hc⟩ : F) y
  simp only [nt]
  rw [show c * y = (⟨c, hc⟩ : F) • y from rfl, this]
  rfl

theorem nt_of_mem {y : PadicAlgCl p} (hy : y ∈ F) : nt F y = y := by
  have := Algebra.normalizedTrace_algebraMap_apply_eq_self F (PadicAlgCl p) ⟨y, hy⟩
  simp only [nt]
  rw [show y = algebraMap F (PadicAlgCl p) ⟨y, hy⟩ from rfl, this]
  rfl

theorem nt_sum {ι : Type*} (s : Finset ι) (f : ι → PadicAlgCl p) :
    nt F (∑ i ∈ s, f i) = ∑ i ∈ s, nt F (f i) := by
  simp [nt]

/-- The normalised trace via the minimal polynomial. -/
theorem nt_eq_nextCoeff (y : PadicAlgCl p) :
    nt F y = ((minpoly F y).natDegree : PadicAlgCl p)⁻¹ * -(mp F y).nextCoeff := by
  rw [nt, Algebra.normalizedTrace_minpoly, mp, nextCoeff_map (algebraMap F _).injective]
  simp

/-- Transitivity of normalised traces: `nt_F ∘ nt_{F'} = nt_F` for `F ⊆ F'`. -/
theorem nt_nt {F F' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : F ≤ F') (y : PadicAlgCl p) :
    nt F (nt F' y) = nt F y := by
  letI : Algebra F F' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F F' (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral F F' := ⟨fun x =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom F F' (PadicAlgCl p))
      (algebraMap F' (PadicAlgCl p)).injective).mp (isIntegral_over F (x : PadicAlgCl p))⟩
  have h1 := Algebra.normalizedTrace_trans_apply F F' (PadicAlgCl p) y
  have h2 := Algebra.normalizedTrace_algebraMap_apply F F' (PadicAlgCl p)
    (Algebra.normalizedTrace F' (PadicAlgCl p) y)
  simp only [nt]
  rw [← h1, ← h2]
  rfl

theorem norm_multiset_sum_le {s : Multiset (PadicAlgCl p)} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x ∈ s, ‖x‖ ≤ r) : ‖s.sum‖ ≤ r := by
  induction s using Multiset.induction_on with
  | empty => simpa using hr
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h a (Multiset.mem_cons_self _ _))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))

theorem norm_nextCoeff_mp_le (y : PadicAlgCl p) : ‖(mp F y).nextCoeff‖ ≤ ‖y‖ := by
  rw [Splits.nextCoeff_eq_neg_sum_roots_of_monic (IsAlgClosed.splits _) (mp_monic F y), norm_neg]
  refine norm_multiset_sum_le (norm_nonneg _) fun w hw => ?_
  exact (norm_eq_of_isRoot_mp F ((mem_roots (mp_ne_zero F y)).mp hw)).le

/-! ### Relative degrees and traces -/

/-- The relative degree `[N : F] = [N : ℚ_p] / [F : ℚ_p]`. -/
def rdeg (F N : IntermediateField ℚ_[p] (PadicAlgCl p)) : ℕ := finrank ℚ_[p] N / finrank ℚ_[p] F

/-- `[F(y) : ℚ_p] = [F : ℚ_p] [F(y) : F]`. -/
theorem finrank_restrictScalars_adjoin (y : PadicAlgCl p) :
    finrank ℚ_[p] ((F⟮y⟯).restrictScalars ℚ_[p]) = finrank ℚ_[p] F * (minpoly F y).natDegree := by
  have h1 := Module.finrank_mul_finrank ℚ_[p] F F⟮y⟯
  rw [adjoin.finrank (isIntegral_over F y)] at h1
  rw [h1]
  rfl

theorem finiteDimensional_of_le' {F N : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] N] (h : F ≤ N) : FiniteDimensional ℚ_[p] F :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective

theorem rdeg_mul {F N L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
    (hFN : F ≤ N) (hNL : N ≤ L) : rdeg F L = rdeg F N * rdeg N L := by
  have h1 := finrank_dvd_of_le_right (K := ℚ_[p]) hFN
  have h2 := finrank_dvd_of_le_right (K := ℚ_[p]) hNL
  haveI : FiniteDimensional ℚ_[p] N := finiteDimensional_of_le' hNL
  haveI : FiniteDimensional ℚ_[p] F := finiteDimensional_of_le' hFN
  have hF0 : 0 < finrank ℚ_[p] F := finrank_pos
  have hN0 : 0 < finrank ℚ_[p] N := finrank_pos
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hFa : 0 < finrank ℚ_[p] F * a := ha ▸ hN0
  simp only [rdeg, hb, ha]
  rw [Nat.mul_div_cancel_left _ hFa, mul_assoc, Nat.mul_div_cancel_left _ hF0,
    Nat.mul_div_cancel_left _ hF0]

theorem rdeg_adjoin {F N : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] F]
    {y : PadicAlgCl p} (hN : (F⟮y⟯).restrictScalars ℚ_[p] = N) :
    rdeg F N = (minpoly F y).natDegree := by
  have hF0 : 0 < finrank ℚ_[p] F := finrank_pos
  rw [rdeg, ← hN, finrank_restrictScalars_adjoin, Nat.mul_div_cancel_left _ hF0]

theorem le_restrictScalars_adjoin (y : PadicAlgCl p) : F ≤ (F⟮y⟯).restrictScalars ℚ_[p] :=
  fun x hx => (F⟮y⟯).algebraMap_mem ⟨x, hx⟩

theorem mem_restrictScalars_adjoin (y : PadicAlgCl p) : y ∈ (F⟮y⟯).restrictScalars ℚ_[p] :=
  mem_adjoin_simple_self F y

theorem restrictScalars_adjoin_le {N : IntermediateField ℚ_[p] (PadicAlgCl p)} (hFN : F ≤ N)
    {y : PadicAlgCl p} (hy : y ∈ N) : (F⟮y⟯).restrictScalars ℚ_[p] ≤ N := by
  intro x hx
  have : F⟮y⟯ ≤ IntermediateField.extendScalars hFN := adjoin_simple_le_iff.mpr hy
  exact this hx

/-- **Trace bound.** `‖Tr_{N/F}(y)‖ ≤ ‖y‖` for `y ∈ N`, `Tr_{N/F} = [N : F] nt_F`. -/
theorem norm_rdeg_mul_nt_le {N : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] N] (hFN : F ≤ N) {y : PadicAlgCl p} (hy : y ∈ N) :
    ‖(rdeg F N : PadicAlgCl p) * nt F y‖ ≤ ‖y‖ := by
  haveI : FiniteDimensional ℚ_[p] F := finiteDimensional_of_le' hFN
  set E := (F⟮y⟯).restrictScalars ℚ_[p]
  have hE : rdeg F E = (minpoly F y).natDegree := rdeg_adjoin rfl
  rw [rdeg_mul (le_restrictScalars_adjoin F y) (restrictScalars_adjoin_le F hFN hy), hE,
    nt_eq_nextCoeff]
  have hd : ((minpoly F y).natDegree : PadicAlgCl p) ≠ 0 :=
    Nat.cast_ne_zero.mpr (minpoly.natDegree_pos (isIntegral_over F y)).ne'
  rw [show ((((minpoly F y).natDegree * rdeg E N : ℕ)) : PadicAlgCl p) *
      (((minpoly F y).natDegree : PadicAlgCl p)⁻¹ * -(mp F y).nextCoeff) =
      (rdeg E N : PadicAlgCl p) * -(mp F y).nextCoeff by
    push_cast; field_simp]
  rw [norm_mul, norm_neg]
  calc ‖(rdeg E N : PadicAlgCl p)‖ * ‖(mp F y).nextCoeff‖ ≤ 1 * ‖y‖ :=
        mul_le_mul (norm_natCast_le_one' _) (norm_nextCoeff_mp_le F y) (norm_nonneg _) zero_le_one
    _ = ‖y‖ := one_mul _

end PadicHodge
