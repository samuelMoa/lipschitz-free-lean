import Mathlib

/-!
# C. Petitjean, A. Procházka, "On exposed points of Lipschitz free spaces"
(arXiv:1810.12031, 2018)

Personal formalization test of the proofs contained in the paper.
The authors are not associated with this test.

The results that the paper borrows from other works are ASSUMED. They are not
declared as axioms: they appear as explicit hypotheses of the statements.
Lean therefore checks the implication "cited results ⇒ results of the paper".

Assumed results:
* standard properties of F(M) (Godefroy–Kalton [7]): structure `FreeSpaceFacts`;
* Lemma 2.23 of [4] (Fabian et al.): `Lemma223`;
* Proposition 2 (Aliaga–Pernecká [2]): `Prop2`;
* Lemma 5 (properties of the magic function, proved in [8]): `Lemma5`.

Proved results: Lemma 3, Lemma 4, the remark after Lemma 5,
Lemma 6 and Theorem 1 (with base point q, as in the proof of the paper).
-/

open Set Metric Filter Topology Classical

noncomputable section

namespace PetitjeanProchazka

variable {M : Type*} [MetricSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Definitions of the paper -/

/-- The molecule `m_xy = (δ(x) - δ(y)) / d(x,y)`. -/
def mol (δ : M → F) (x y : M) : F := (dist x y)⁻¹ • (δ x - δ y)

/-- `F(N)`: closure of the span of the `δ(x)`, `x ∈ N`. -/
def FN (δ : M → F) (N : Set M) : Submodule ℝ F :=
  (Submodule.span ℝ (δ '' N)).topologicalClosure

/-- `M̃ = M × M` minus the diagonal. -/
abbrev Mt (M : Type*) := {pr : M × M // pr.1 ≠ pr.2}

/-- The metric segment `[p,q]`. -/
def seg (p q : M) : Set M := {x | dist p x + dist x q = dist p q}

/-- The set `[p,q]_ε`. -/
def segEps (p q : M) (ε : ℝ) : Set M := {x | dist p x + dist x q ≤ (1 - ε)⁻¹ * dist p q}

/-- The "magic function" `f_pq` (base point `o`). -/
def magic (o p q : M) (t : M) : ℝ :=
  dist p q / 2 * ((dist t q - dist t p) / (dist t q + dist t p)
    - (dist o q - dist o p) / (dist o q + dist o p))

/-! ## Assumed results -/

/-- Standard properties of `F(M)` (Godefroy–Kalton [7]): `ev f` is the linear
form `⟨·, f⟩` associated with `f ∈ Lip₀(M)`. -/
structure FreeSpaceFacts (o : M) (δ : M → F) (ev : (M → ℝ) → F →L[ℝ] ℝ) : Prop where
  ev_delta : ∀ f : M → ℝ, LipschitzWith 1 f → f o = 0 → ∀ x, ev f (δ x) = f x
  ev_norm : ∀ f : M → ℝ, LipschitzWith 1 f → f o = 0 → ‖ev f‖ ≤ 1
  delta_base : δ o = 0
  norm_delta_sub : ∀ x y, ‖δ x - δ y‖ ≤ dist x y
  ball_subset : ball (0 : F) 1 ⊆ closure (convexHull ℝ (range fun i : Mt M => mol δ i.1.1 i.1.2))

/-- Lemma 2.23 of [4] (Fabian et al.). -/
def Lemma223 (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : Prop :=
  ∀ T : X →L[ℝ] Y, ball (0 : Y) 1 ⊆ closure (T '' ball (0 : X) 1) →
    ball (0 : Y) 1 ⊆ T '' ball (0 : X) 1

/-- Proposition 2 (Aliaga–Pernecká [2]), in the form used in the proof of
Theorem 1 (closed families containing the base point, inside a common ball). -/
def Prop2 (o : M) (δ : M → F) : Prop :=
  ∀ (S : Set ℝ) (N : ℝ → Set M), S.Nonempty → (∀ α ∈ S, IsClosed (N α)) →
    (∀ α ∈ S, o ∈ N α) → (∃ R, ∀ α ∈ S, N α ⊆ closedBall o R) →
    (⋂ α ∈ S, (FN δ (N α) : Set F)) = (FN δ (⋂ α ∈ S, N α) : Set F)

/-- Lemma 5 of the paper (properties of `f_pq`, proved in [8]). -/
def Lemma5 (o : M) : Prop :=
  ∀ p q : M, p ≠ q →
    LipschitzWith 1 (magic o p q) ∧
    (∀ u v : M, u ≠ v → ∀ ε : ℝ, 0 < ε → ε < 1 →
      1 - ε < (magic o p q u - magic o p q v) / dist u v →
        u ∈ segEps p q ε ∧ v ∈ segEps p q ε) ∧
    (∀ u v : M, u ≠ v → (magic o p q u - magic o p q v) / dist u v = 1 →
      u ∈ seg p q ∧ v ∈ seg p q)

/-! ## Elementary lemmas -/

section Basic

variable {o : M} {δ : M → F} {ev : (M → ℝ) → F →L[ℝ] ℝ}

lemma ev_mol (hF : FreeSpaceFacts o δ ev) {f : M → ℝ} (hf : LipschitzWith 1 f) (hf0 : f o = 0)
    (x y : M) : ev f (mol δ x y) = (f x - f y) / dist x y := by
  simp only [mol, map_smul, map_sub, hF.ev_delta f hf hf0, smul_eq_mul]
  ring

lemma norm_mol_le (hF : FreeSpaceFacts o δ ev) {x y : M} (hxy : x ≠ y) : ‖mol δ x y‖ ≤ 1 := by
  have hd : 0 < dist x y := dist_pos.2 hxy
  rw [mol, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
  calc (dist x y)⁻¹ * ‖δ x - δ y‖ ≤ (dist x y)⁻¹ * dist x y :=
        mul_le_mul_of_nonneg_left (hF.norm_delta_sub x y) (inv_nonneg.2 hd.le)
    _ = 1 := inv_mul_cancel₀ hd.ne'

lemma abs_ev_mol_le (hF : FreeSpaceFacts o δ ev) {f : M → ℝ} (hf : LipschitzWith 1 f)
    (hf0 : f o = 0) {x y : M} (hxy : x ≠ y) : |ev f (mol δ x y)| ≤ 1 := by
  have hd : 0 < dist x y := dist_pos.2 hxy
  rw [ev_mol hF hf hf0, abs_div, abs_of_pos hd, div_le_one hd]
  have := hf.dist_le_mul x y
  rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this

lemma isClosed_FN (N : Set M) : IsClosed (FN δ N : Set F) :=
  Submodule.isClosed_topologicalClosure _

lemma delta_mem_FN {N : Set M} {x : M} (hx : x ∈ N) : δ x ∈ FN δ N :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_image_of_mem δ hx))

lemma mol_mem_FN {N : Set M} {x y : M} (hx : x ∈ N) (hy : y ∈ N) : mol δ x y ∈ FN δ N :=
  Submodule.smul_mem _ _ (Submodule.sub_mem _ (delta_mem_FN hx) (delta_mem_FN hy))

lemma tsum_mem_FN {ι : Type*} {N : Set M} {g : ι → F} (hg : ∀ i, g i ∈ FN δ N) :
    ∑' i, g i ∈ FN δ N := by
  by_cases hs : Summable g
  · exact (isClosed_FN N).mem_of_tendsto hs.hasSum
      (Eventually.of_forall fun s => Submodule.sum_mem _ fun i _ => hg i)
  · rw [tsum_eq_zero_of_not_summable hs]
    exact Submodule.zero_mem _

lemma magic_sub (o : M) {p q : M} (hpq : p ≠ q) : magic o p q p - magic o p q q = dist p q := by
  have hd : 0 < dist p q := dist_pos.2 hpq
  simp only [magic, dist_self, sub_zero, zero_sub, add_zero, zero_add, dist_comm q p]
  rw [div_self hd.ne', neg_div, div_self hd.ne']
  ring

lemma magic_base (o p q : M) : magic o p q o = 0 := by simp [magic]

end Basic

/-! ## The space ℓ₁ -/

section L1

variable {ι : Type*}

lemma summable_abs_lp (a : lp (fun _ : ι => ℝ) 1) : Summable fun i => |a i| := by
  have := (lp.memℓp a).summable (by norm_num : 0 < (1 : ENNReal).toReal)
  simpa [Real.norm_eq_abs] using this

lemma norm_lp_one (a : lp (fun _ : ι => ℝ) 1) : ‖a‖ = ∑' i, |a i| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp [Real.norm_eq_abs]

end L1

/-! ## Lemma 3 -/

section Lemma3

variable {o : M} {δ : M → F} {ev : (M → ℝ) → F →L[ℝ] ℝ} [CompleteSpace F]

lemma norm_coef_mol_le (hF : FreeSpaceFacts o δ ev) (c : ℝ) (i : Mt M) :
    ‖c • mol δ i.1.1 i.1.2‖ ≤ |c| := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_mol_le hF i.2)

lemma summable_coef_mol (hF : FreeSpaceFacts o δ ev) {c : Mt M → ℝ}
    (hc : Summable fun i => |c i|) : Summable fun i : Mt M => c i • mol δ i.1.1 i.1.2 :=
  Summable.of_norm_bounded hc fun i => norm_coef_mol_le hF (c i) i

lemma summable_norm_coef_mol (hF : FreeSpaceFacts o δ ev) {c : Mt M → ℝ}
    (hc : Summable fun i => |c i|) :
    Summable fun i : Mt M => ‖c i • mol δ i.1.1 i.1.2‖ :=
  hc.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => norm_coef_mol_le hF (c i) i

/-- The operator `Q : ℓ₁(M̃) → F(M)`, `e_(x,y) ↦ m_xy`. -/
def Qmap (hF : FreeSpaceFacts o δ ev) : lp (fun _ : Mt M => ℝ) 1 →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' i : Mt M, a i • mol δ i.1.1 i.1.2
      map_add' := fun a b => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_coef_mol hF (summable_abs_lp a)).tsum_add
          (summable_coef_mol hF (summable_abs_lp b))
      map_smul' := fun c a => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (summable_coef_mol hF (summable_abs_lp a)).tsum_const_smul c }
    1 fun a => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [norm_lp_one]
      exact (norm_tsum_le_tsum_norm (summable_norm_coef_mol hF (summable_abs_lp a))).trans
        ((summable_norm_coef_mol hF (summable_abs_lp a)).tsum_le_tsum
          (fun i => norm_coef_mol_le hF (a i) i) (summable_abs_lp a))

lemma Qmap_apply (hF : FreeSpaceFacts o δ ev) (a : lp (fun _ : Mt M => ℝ) 1) :
    Qmap hF a = ∑' i : Mt M, a i • mol δ i.1.1 i.1.2 := rfl

lemma Qmap_single (hF : FreeSpaceFacts o δ ev) (i : Mt M) :
    Qmap hF (lp.single 1 i (1 : ℝ)) = mol δ i.1.1 i.1.2 := by
  rw [Qmap_apply, tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

/-- **Lemma 3.** `Q` has norm at most 1 and the image of the open unit ball
contains the open unit ball of `F(M)` (in particular `Q` is onto). -/
theorem lemma3 (hF : FreeSpaceFacts o δ ev) (h223 : Lemma223 (lp (fun _ : Mt M => ℝ) 1) F) :
    ‖Qmap hF‖ ≤ 1 ∧ ball (0 : F) 1 ⊆ Qmap hF '' ball 0 1 := by
  refine ⟨LinearMap.mkContinuous_norm_le _ zero_le_one _, h223 _ ?_⟩
  set Q := Qmap hF
  have hV : range (fun i : Mt M => mol δ i.1.1 i.1.2) ⊆ Q '' closedBall 0 1 := by
    rintro _ ⟨i, rfl⟩
    refine ⟨lp.single 1 i 1, ?_, Qmap_single hF i⟩
    rw [mem_closedBall_zero_iff, lp.norm_single (by norm_num)]
    simp
  have hconv : convexHull ℝ (range fun i : Mt M => mol δ i.1.1 i.1.2) ⊆ Q '' closedBall 0 1 :=
    convexHull_min hV
      ((convex_closedBall (0 : lp (fun _ : Mt M => ℝ) 1) 1).linear_image
        (Q : lp (fun _ : Mt M => ℝ) 1 →ₗ[ℝ] F))
  have hcl : Q '' closedBall (0 : lp (fun _ : Mt M => ℝ) 1) 1 ⊆ closure (Q '' ball 0 1) := by
    rw [← closure_ball (0 : lp (fun _ : Mt M => ℝ) 1) one_ne_zero]
    exact image_closure_subset_closure_image Q.continuous
  calc ball (0 : F) 1 ⊆ closure (convexHull ℝ (range fun i : Mt M => mol δ i.1.1 i.1.2)) :=
        hF.ball_subset
    _ ⊆ closure (Q '' closedBall 0 1) := closure_mono hconv
    _ ⊆ closure (closure (Q '' ball 0 1)) := closure_mono hcl
    _ = closure (Q '' ball 0 1) := closure_closure

/-- Consequence of Lemma 3 used in the proof of Lemma 6. -/
lemma exists_rep (hF : FreeSpaceFacts o δ ev) (h223 : Lemma223 (lp (fun _ : Mt M => ℝ) 1) F)
    (μ : F) {η : ℝ} (hη : 0 < η) :
    ∃ a : lp (fun _ : Mt M => ℝ) 1, Qmap hF a = μ ∧ ‖a‖ < ‖μ‖ + η := by
  set s := ‖μ‖ + η with hsdef
  have hs : 0 < s := by positivity
  have hm : s⁻¹ • μ ∈ ball (0 : F) 1 := by
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_lt_iff₀ hs]
    linarith
  obtain ⟨b, hb, hbμ⟩ := (lemma3 hF h223).2 hm
  refine ⟨s • b, ?_, ?_⟩
  · rw [map_smul, hbμ, smul_inv_smul₀ hs.ne']
  · rw [mem_ball_zero_iff] at hb
    rw [norm_smul, Real.norm_of_nonneg hs.le]
    nlinarith [norm_nonneg b]

end Lemma3

/-! ## Lemma 4 -/

/-- **Lemma 4.** (stated for a family indexed by an arbitrary set) -/
theorem lemma4 {ι : Type*} (a b : ι → ℝ) (ha : Summable fun i => |a i|)
    (ha1 : ∑' i, |a i| = 1) (hb : ∀ i, |b i| ≤ 1) {α ε : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hε : 0 < ε) (hε1 : ε < 1) (h : 1 - α * ε ≤ ∑' i, a i * b i) :
    ∑' i, {i | |b i| ≤ 1 - α}.indicator (fun i => |a i|) i ≤ ε := by
  set B := {i | |b i| ≤ 1 - α}
  have hind : Summable fun i => B.indicator (fun i => |a i|) i :=
    ha.of_nonneg_of_le (fun i => Set.indicator_nonneg (fun _ _ => abs_nonneg _) i)
      (fun i => Set.indicator_le_self' (fun _ _ => abs_nonneg _) i)
  have hab : Summable fun i => a i * b i :=
    Summable.of_norm_bounded ha fun i => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hb i)
  have key : ∀ i, a i * b i ≤ |a i| - α * B.indicator (fun i => |a i|) i := by
    intro i
    by_cases hi : i ∈ B
    · simp only [Set.indicator_apply, hi, if_true]
      have h1 : |a i * b i| ≤ |a i| * (1 - α) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
      nlinarith [le_abs_self (a i * b i)]
    · simp only [Set.indicator_apply, hi, if_false, mul_zero, sub_zero]
      calc a i * b i ≤ |a i * b i| := le_abs_self _
        _ = |a i| * |b i| := abs_mul _ _
        _ ≤ |a i| := mul_le_of_le_one_right (abs_nonneg _) (hb i)
  have hsum : ∑' i, a i * b i ≤ 1 - α * ∑' i, B.indicator (fun i => |a i|) i := by
    calc ∑' i, a i * b i ≤ ∑' i, (|a i| - α * B.indicator (fun i => |a i|) i) :=
          hab.tsum_le_tsum key (ha.sub (hind.mul_left α))
      _ = 1 - α * ∑' i, B.indicator (fun i => |a i|) i := by
          rw [ha.tsum_sub (hind.mul_left α), tsum_mul_left, ha1]
  have : α * ∑' i, B.indicator (fun i => |a i|) i ≤ α * ε := by linarith
  exact le_of_mul_le_mul_left this hα

/-! ## Remark after Lemma 5 -/

section Remark

variable {o : M} {δ : M → F} {ev : (M → ℝ) → F →L[ℝ] ℝ}

/-- If `[p,q] = {p,q}`, `f_pq` exposes `m_pq` among molecules. -/
theorem remark_molecules (hF : FreeSpaceFacts o δ ev) (hL5 : Lemma5 o) {p q : M}
    (hpq : p ≠ q) (hseg : seg p q = {p, q}) {u v : M} (huv : u ≠ v)
    (h : ev (magic o p q) (mol δ u v) = 1) : u = p ∧ v = q := by
  obtain ⟨hlip, -, h53⟩ := hL5 p q hpq
  rw [ev_mol hF hlip (magic_base o p q)] at h
  obtain ⟨hu, hv⟩ := h53 u v huv h
  rw [hseg] at hu hv
  simp only [mem_insert_iff, mem_singleton_iff] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact absurd (hu.trans hv.symm) huv
  · exact ⟨hu, hv⟩
  · exfalso
    rw [hu, hv] at h
    rw [dist_comm q p, show magic o p q q - magic o p q p = -(magic o p q p - magic o p q q) by ring,
      magic_sub o hpq, neg_div, div_self (dist_pos.2 hpq).ne'] at h
    norm_num at h
  · exact absurd (hu.trans hv.symm) huv

end Remark

/-! ## Lemma 6 -/

section Lemma6

variable {o : M} {δ : M → F} {ev : (M → ℝ) → F →L[ℝ] ℝ} [CompleteSpace F]

/-- **Lemma 6.** -/
theorem lemma6 (hF : FreeSpaceFacts o δ ev) (h223 : Lemma223 (lp (fun _ : Mt M => ℝ) 1) F)
    (hL5 : Lemma5 o) {p q : M} (hpq : p ≠ q) (hbase : o = q) (hseg : seg p q = {p, q})
    {μ : F} (hμ : ‖μ‖ ≤ 1) (h1 : ev (magic o p q) μ = 1)
    {ε α : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hα : 0 < α) (hα2 : α < 1 / 2) :
    ∃ ν ∈ FN δ (segEps p q α), ‖μ - ν‖ ≤ 2 * ε := by
  obtain ⟨hlip, h52, -⟩ := hL5 p q hpq
  set f := magic o p q with hfdef
  have hf0 : f o = 0 := magic_base o p q
  -- "by the hypothesis ‖μ‖ = 1" (quoted from the paper)
  have hμ1 : ‖μ‖ = 1 := by
    have h := (ev f).le_opNorm μ
    have hn := hF.ev_norm f hlip hf0
    rw [h1, norm_one] at h
    nlinarith [norm_nonneg μ, norm_nonneg (ev f)]
  -- representation given by Lemma 3
  have hea : 0 < ε * α := mul_pos hε hα
  have hea1 : ε * α < 1 / 4 := by nlinarith
  set η := ε * α / (1 - ε * α) with hηdef
  have hη : 0 < η := div_pos hea (by linarith)
  have hη_eq : η * (1 - ε * α) = ε * α := div_mul_cancel₀ _ (by linarith)
  have hη_le : η ≤ 1 := by rw [hηdef, div_le_one (by linarith)]; linarith
  obtain ⟨a, hQa, ha⟩ := exists_rep hF h223 μ hη
  rw [hμ1] at ha
  have ha_ge : 1 ≤ ‖a‖ := by
    calc (1 : ℝ) = ‖μ‖ := hμ1.symm
      _ = ‖Qmap hF a‖ := by rw [hQa]
      _ ≤ ‖Qmap hF‖ * ‖a‖ := (Qmap hF).le_opNorm a
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (lemma3 hF h223).1 (norm_nonneg _)
      _ = ‖a‖ := one_mul _
  have hapos : 0 < ‖a‖ := by linarith
  -- the coefficients b_i = ⟨m_{p_i q_i}, f_pq⟩
  set b : Mt M → ℝ := fun i => ev f (mol δ i.1.1 i.1.2) with hbdef
  have hb : ∀ i, |b i| ≤ 1 := fun i => abs_ev_mol_le hF hlip hf0 i.2
  have hsa := summable_abs_lp a
  have hsumm := summable_coef_mol (δ := δ) hF hsa
  have hev : ev f μ = ∑' i, a i * b i := by
    rw [← hQa, Qmap_apply, (ev f).map_tsum hsumm]
    simp only [map_smul, smul_eq_mul, hbdef]
  -- normalisation a / ‖a‖
  set a' : Mt M → ℝ := fun i => a i / ‖a‖ with ha'def
  have ha'abs : Summable fun i => |a' i| := by
    simpa [ha'def, abs_div, abs_of_pos hapos] using hsa.div_const ‖a‖
  have ha'1 : ∑' i, |a' i| = 1 := by
    simp only [ha'def, abs_div, abs_norm]
    rw [tsum_div_const, ← norm_lp_one, div_self hapos.ne']
  have hlow : 1 - α * ε ≤ ∑' i, a' i * b i := by
    have e : ∑' i, a' i * b i = (∑' i, a i * b i) / ‖a‖ := by
      simp only [ha'def, div_mul_eq_mul_div]
      rw [tsum_div_const]
    rw [e, ← hev, h1, le_div_iff₀ hapos]
    nlinarith
  have hL4 := lemma4 a' b ha'abs ha'1 hb hα (by linarith) hε (by linarith) hlow
  set B := {i : Mt M | |b i| ≤ 1 - α} with hBdef
  -- Σ_{i ∈ B} |a_i| ≤ 2ε
  have hBsum : ∑' i, B.indicator (fun i => |a i|) i ≤ 2 * ε := by
    have e : ∑' i, B.indicator (fun i => |a i|) i
        = ‖a‖ * ∑' i, B.indicator (fun i => |a' i|) i := by
      rw [← tsum_mul_left]
      congr 1
      ext i
      by_cases hi : i ∈ B
      · simp only [Set.indicator_apply, hi, if_true, ha'def, abs_div, abs_norm]
        field_simp
      · simp only [Set.indicator_apply, hi, if_false, mul_zero]
    rw [e]
    calc ‖a‖ * ∑' i, B.indicator (fun i => |a' i|) i ≤ ‖a‖ * ε :=
          mul_le_mul_of_nonneg_left hL4 hapos.le
      _ ≤ 2 * ε := by nlinarith
  -- for i ∉ B, p_i and q_i lie in [p,q]_α (Lemma 5 (2))
  have hgood : ∀ i, i ∉ B → i.1.1 ∈ segEps p q α ∧ i.1.2 ∈ segEps p q α := by
    intro i hi
    simp only [hBdef, mem_setOf_eq, not_le] at hi
    have hbi : b i = (f i.1.1 - f i.1.2) / dist i.1.1 i.1.2 := ev_mol hF hlip hf0 _ _
    rcases lt_abs.1 hi with h | h
    · exact h52 _ _ i.2 α hα (by linarith) (by rw [← hbi]; exact h)
    · have h' := h52 i.1.2 i.1.1 (Ne.symm i.2) α hα (by linarith) (by
        rw [dist_comm, show f i.1.2 - f i.1.1 = -(f i.1.1 - f i.1.2) by ring, neg_div, ← hbi]
        linarith)
      exact ⟨h'.2, h'.1⟩
  -- splitting μ = ν + (μ - ν)
  have hsG : Summable fun i => |Bᶜ.indicator (fun i => a i) i| :=
    hsa.of_nonneg_of_le (fun _ => abs_nonneg _) fun i => by
      by_cases hi : i ∈ Bᶜ <;> simp [Set.indicator_apply, hi]
  have hsB : Summable fun i => |B.indicator (fun i => a i) i| :=
    hsa.of_nonneg_of_le (fun _ => abs_nonneg _) fun i => by
      by_cases hi : i ∈ B <;> simp [Set.indicator_apply, hi]
  set ν := ∑' i, Bᶜ.indicator (fun i => a i) i • mol δ i.1.1 i.1.2 with hνdef
  refine ⟨ν, tsum_mem_FN fun i => ?_, ?_⟩
  · by_cases hi : i ∈ B
    · simp [Set.indicator_apply, hi]
    · have hi' : i ∈ Bᶜ := hi
      simp only [Set.indicator_apply, hi', if_true]
      exact Submodule.smul_mem _ _ (mol_mem_FN (hgood i hi).1 (hgood i hi).2)
  · have hdiff : μ - ν = ∑' i, B.indicator (fun i => a i) i • mol δ i.1.1 i.1.2 := by
      rw [← hQa, Qmap_apply, hνdef, ← hsumm.tsum_sub (summable_coef_mol hF hsG)]
      congr 1
      ext i
      by_cases hi : i ∈ B
      · simp [Set.indicator_apply, hi]
      · simp [Set.indicator_apply, hi]
    rw [hdiff]
    calc ‖∑' i, B.indicator (fun i => a i) i • mol δ i.1.1 i.1.2‖
        ≤ ∑' i, ‖B.indicator (fun i => a i) i • mol δ i.1.1 i.1.2‖ :=
          norm_tsum_le_tsum_norm (summable_norm_coef_mol hF hsB)
      _ ≤ ∑' i, |B.indicator (fun i => a i) i| :=
          (summable_norm_coef_mol hF hsB).tsum_le_tsum (fun i => norm_coef_mol_le hF _ i) hsB
      _ = ∑' i, B.indicator (fun i => |a i|) i := by
          congr 1
          ext i
          by_cases hi : i ∈ B <;> simp [Set.indicator_apply, hi]
      _ ≤ 2 * ε := hBsum

end Lemma6

/-! ## Theorem 1 -/

section Theorem1

lemma isClosed_segEps (p q : M) (α : ℝ) : IsClosed (segEps p q α) :=
  isClosed_le ((continuous_const.dist continuous_id).add (continuous_id.dist continuous_const))
    continuous_const

lemma iInter_segEps (p q : M) : ⋂ α ∈ Ioo (0 : ℝ) (1 / 2), segEps p q α = seg p q := by
  ext x
  simp only [mem_iInter₂, segEps, seg, mem_setOf_eq, mem_Ioo]
  constructor
  · intro h
    refine le_antisymm ?_ (dist_triangle p x q)
    by_contra hc
    push_neg at hc
    set s := dist p x + dist x q
    set d := dist p q
    have hd0 : 0 ≤ d := dist_nonneg
    have hs : 0 < s := by linarith
    set α := min (1 / 4) ((s - d) / (2 * s)) with hαdef
    have hα0 : 0 < α := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hα1 : α ≤ 1 / 4 := min_le_left _ _
    have hα2 : α ≤ (s - d) / (2 * s) := min_le_right _ _
    have key : s * α ≤ (s - d) / 2 := by
      calc s * α ≤ s * ((s - d) / (2 * s)) := mul_le_mul_of_nonneg_left hα2 hs.le
        _ = (s - d) / 2 := by field_simp
    have hle := h α ⟨hα0, by linarith⟩
    rw [le_inv_mul_iff₀ (by linarith : (0 : ℝ) < 1 - α)] at hle
    nlinarith
  · intro h α hα
    rw [h]
    exact le_mul_of_one_le_left dist_nonneg
      ((one_le_inv₀ (by linarith [hα.2])).2 (by linarith [hα.1]))

variable {o : M} {δ : M → F} {ev : (M → ℝ) → F →L[ℝ] ℝ} [CompleteSpace F]

/-- **Theorem 1** (proof of the paper, base point `q`): if `[p,q] = {p,q}`,
the molecule `m_pq` is an exposed point of the unit ball of `F(M)`,
exposed by the magic function `f_pq`. -/
theorem theorem1 [CompleteSpace M] (hF : FreeSpaceFacts o δ ev)
    (h223 : Lemma223 (lp (fun _ : Mt M => ℝ) 1) F) (hP2 : Prop2 o δ) (hL5 : Lemma5 o)
    {p q : M} (hpq : p ≠ q) (hseg : seg p q = {p, q}) (hbase : o = q) :
    mol δ p q ∈ (closedBall (0 : F) 1).exposedPoints ℝ := by
  obtain ⟨hlip, -, -⟩ := hL5 p q hpq
  set f := magic o p q with hfdef
  have hf0 : f o = 0 := magic_base o p q
  have hd : 0 < dist p q := dist_pos.2 hpq
  have hlm : ev f (mol δ p q) = 1 := by
    rw [ev_mol hF hlip hf0, hfdef, magic_sub o hpq, div_self hd.ne']
  have hmem : mol δ p q ∈ closedBall (0 : F) 1 := mem_closedBall_zero_iff.2 (norm_mol_le hF hpq)
  have hle : ∀ μ ∈ closedBall (0 : F) 1, ev f μ ≤ 1 := fun μ hμ => by
    rw [mem_closedBall_zero_iff] at hμ
    have h := (ev f).le_opNorm μ
    have hn := hF.ev_norm f hlip hf0
    rw [Real.norm_eq_abs] at h
    nlinarith [le_abs_self (ev f μ), norm_nonneg μ, norm_nonneg (ev f)]
  refine ⟨hmem, ev f, fun μ hμ => ⟨by rw [hlm]; exact hle μ hμ, fun hge => ?_⟩⟩
  rw [hlm] at hge
  have h1 : ev f μ = 1 := le_antisymm (hle μ hμ) hge
  -- Lemma 6: μ ∈ ⋂_{α} F([p,q]_α)
  set S : Set ℝ := Ioo 0 (1 / 2) with hSdef
  have hin : ∀ α ∈ S, μ ∈ FN δ (segEps p q α) := by
    rintro α ⟨hα, hα2⟩
    have hcl : μ ∈ closure (FN δ (segEps p q α) : Set F) := by
      rw [Metric.mem_closure_iff]
      intro e he
      have he4 : 0 < min (1 / 4) (e / 4) := lt_min (by norm_num) (by linarith)
      obtain ⟨ν, hν, hdist⟩ := lemma6 hF h223 hL5 hpq hbase hseg
        (mem_closedBall_zero_iff.1 hμ) h1 he4
        (lt_of_le_of_lt (min_le_left _ _) (by norm_num)) hα hα2
      refine ⟨ν, hν, ?_⟩
      rw [dist_eq_norm]
      have := min_le_right (1 / 4 : ℝ) (e / 4)
      linarith
    rwa [(isClosed_FN (δ := δ) _).closure_eq] at hcl
  -- Proposition 2
  have hP := hP2 S (segEps p q) ⟨1 / 4, by norm_num [hSdef]⟩
    (fun α _ => isClosed_segEps p q α)
    (fun α hα => by
      rw [hbase]
      show dist p q + dist q q ≤ (1 - α)⁻¹ * dist p q
      rw [dist_self, add_zero]
      exact le_mul_of_one_le_left dist_nonneg ((one_le_inv₀ (by linarith [hα.2])).2
        (by linarith [hα.1])))
    ⟨2 * dist p q, fun α hα x hx => by
      rw [mem_closedBall, hbase]
      have hx' : dist p x + dist x q ≤ (1 - α)⁻¹ * dist p q := hx
      have h2 : (1 - α)⁻¹ * dist p q ≤ 2 * dist p q := by
        rw [inv_mul_le_iff₀ (by linarith [hα.2])]
        nlinarith [hα.1, hα.2]
      linarith [dist_nonneg (x := p) (y := x)]⟩
  have hμ2 : μ ∈ FN δ (⋂ α ∈ S, segEps p q α) := by
    have : μ ∈ ⋂ α ∈ S, (FN δ (segEps p q α) : Set F) := mem_iInter₂.2 hin
    rw [hP] at this
    exact this
  rw [hSdef, iInter_segEps, hseg] at hμ2
  -- F({p,q}) = span{δ(p)} since δ(q) = δ(0) = 0
  have hq0 : δ q = 0 := by rw [← hbase]; exact hF.delta_base
  have hspan : FN δ ({p, q} : Set M) = Submodule.span ℝ {δ p} := by
    unfold FN
    rw [image_pair, hq0, Set.pair_comm, Submodule.span_insert_zero]
    exact (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq
  rw [hspan] at hμ2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hμ2
  have hmolp : mol δ p q = (dist p q)⁻¹ • δ p := by rw [mol, hq0, sub_zero]
  have hevp : ev f (δ p) = dist p q := by
    rw [hmolp, map_smul, smul_eq_mul] at hlm
    field_simp at hlm
    linarith
  rw [← hc, map_smul, smul_eq_mul, hevp] at h1
  have hc' : c = (dist p q)⁻¹ := by field_simp; linarith
  rw [← hc, hc', hmolp]

end Theorem1

end PetitjeanProchazka

-- Checked on 12 Nov 2026 on live.lean-lang.org (Lean v4.36.0-rc2, Mathlib): no errors;
-- the five results depend only on propext, choice, Quot.sound (no sorry).
#print axioms PetitjeanProchazka.lemma3
#print axioms PetitjeanProchazka.lemma4
#print axioms PetitjeanProchazka.remark_molecules
#print axioms PetitjeanProchazka.lemma6
#print axioms PetitjeanProchazka.theorem1
