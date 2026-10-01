module

public import GradedNear.Row.SpecSound

/-!
# Soundness of the row check (`RowCheckCore.rowCheck`, `checkRow`, `checkRows`)

* `rowCheck_sound`: **an accepted row is valid** (`RowNum`): there are `I_u ≥ I_B` and `D_u > 0`
  such that the stored radius is at least `(1+η)(d₁/D_u + η)` and every checked entry satisfies
  `EntValid` for some values `(add, exc)` of its semantics (`SpecSem`, `specVals_sound`): its
  stored feature is at most `(F(hi - anc) + add - 1/6)/√(I_u D_u) - η`, the diagonal numerator
  `D(s - anc) - 1/6` at its offset `s - anc` is positive, and the stored diagonal is at least
  `(1+η) D⁺/D_u` for some `D⁺ ≥ D(s - anc) - 1/6 + exc`. These are the quantities of
  `builder_threshold` (with `d₁ = g(0)/6 = 1/6`);
* `checkRow_sound`, `checkRows_sound`: the rows of a leaf, and the coverage of its columns and
  family terms by checked entries.
-/

@[expose] public section

noncomputable section

open IntervalCore LeafNumCore MeasureTheory Set

namespace GradedNear.Row

open Parabolic

/-- **What a checked entry means**, with `I_u ≥ I_B`, the normalizer `D_u` and the values
`(add, exc)` of its semantics: the entry's response anchor is at most `s` (its offset `s - anc` is
`≥ 0`), its stored feature `v` is at most `(F(hi - anc) + add - 1/6)/√(I_u D_u) - η`, its diagonal
numerator `D(s - anc) - 1/6` is positive, and its stored diagonal is at least `(1+η) D⁺/D_u` for some
`D⁺ ≥ D(s - anc) - 1/6 + exc`. -/
def EntValid (q : Params) (Iu Du : ℝ) (v D : ℤ) (e : RowCheckCore.Ent) (add exc : ℝ) : Prop :=
  SpecSem q e.sp add exc ∧
  (e.anc : ℝ) ≤ q.s ∧
  (v : ℝ) / SR ≤ ((laplace (fpar (2 * (q.γ : ℝ))) (((e.hi : ℝ) - e.anc : ℝ) : ℂ)).re + add -
      1 / 6) / Real.sqrt (Iu * Du) - ηR ∧
  0 < (q.near ∅).Dδ (q.s - e.anc) - 1 / 6 ∧
  ∃ De : ℝ, (q.near ∅).Dδ (q.s - e.anc) - 1 / 6 + exc ≤ De ∧ (1 + ηR) * De / Du ≤ (D : ℝ) / SR

/-- **What a checked row means**: the parameters are good, every cell bound is positive, and there
are `I_u ≥ I_B` and `D_u > 0` with the stored radius at least `(1+η)(1/6/D_u + η)` and every checked
entry valid for some values of its semantics. -/
def RowNum (p : RowCheckCore.RowP) (d : ℤ) (items : List RowCheckCore.Item) : Prop :=
  (ofCore p).Good ∧ (∀ k < p.m, 0 < (ofCore p).Lk k) ∧
  ∃ Iu Du : ℝ, ((ofCore p).near ∅).IB ≤ Iu ∧ 0 < Du ∧
    (1 + ηR) * (1 / 6 / Du + ηR) ≤ (d : ℝ) / SR ∧
    ∀ it ∈ items, ∃ add exc : ℝ, EntValid (ofCore p) Iu Du it.v it.D it.e add exc

/-- A running maximum dominates its start and every term. -/
lemma foldl_rmax {α : Type*} (g : α → ℚ) :
    ∀ (l : List α) (init : ℚ), init ≤ l.foldl (fun acc a => rmax acc (g a)) init ∧
      ∀ a ∈ l, g a ≤ l.foldl (fun acc a => rmax acc (g a)) init
  | [], init => ⟨le_rfl, fun a ha => absurd ha (List.not_mem_nil)⟩
  | b :: l, init => by
    obtain ⟨h1, h2⟩ := foldl_rmax g l (rmax init (g b))
    have hm1 : init ≤ rmax init (g b) := by unfold rmax; split_ifs with h <;> [exact h; exact le_rfl]
    have hm2 : g b ≤ rmax init (g b) := by
      unfold rmax; split_ifs with h <;> [exact le_rfl; exact le_of_lt (not_le.1 h)]
    refine ⟨hm1.trans h1, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hm2.trans h1
    · exact h2 a ha

lemma getD_map_of_lt {α β : Type*} [Inhabited β] (f : α → β) {l : List α} {i : ℕ} (d : α)
    (hi : i < l.length) : (l.map f).getD i default = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

/-- A `mapM` into `Option` pairs every element with its image. -/
lemma mem_zip_of_mapM {α β : Type*} {f : α → Option β} :
    ∀ {l : List α} {out : List β}, l.mapM f = some out →
      ∀ a ∈ l, ∃ b, f a = some b ∧ (a, b) ∈ l.zip out
  | [], _, _, a, ha => absurd ha List.not_mem_nil
  | x :: l, out, h, a, ha => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨z, hz, zs, hzs, h⟩ := h
    subst h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨z, hz, by simp⟩
    · obtain ⟨b, hb, hmem⟩ := mem_zip_of_mapM hzs a ha
      exact ⟨b, hb, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hmem⟩

/-- **An accepted row is valid.** -/
theorem rowCheck_sound {p : RowCheckCore.RowP} {d : ℤ} {xs ds : List ℚ}
    {items : List RowCheckCore.Item} {prec : ℕ}
    (h : RowCheckCore.rowCheck p d xs ds items prec = true) : RowNum p d items := by
  unfold RowCheckCore.rowCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hgood, hd⟩, h⟩ := h
  have hg := good_sound hgood
  split at h
  swap
  · exact absurd h (by simp)
  rename_i IL vals hIL hvals
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hpre, hfeat⟩ := h
  obtain ⟨hLpos, hRiem⟩ := ibUpper_sound hg hIL
  have hLpos' : ∀ k < (ofCore p).m, 0 < (ofCore p).Lk k := fun k hk => hLpos k hk
  have hIB : ((ofCore p).near ∅).IB ≤ IL :=
    (Params.IB_le hg ∅ hLpos' (by norm_num [RowCheckCore.nShort])).trans hRiem
  have hIBpos := Params.IB_pos hg ∅ hLpos'
  have hILpos : (0 : ℝ) < IL := lt_of_lt_of_le hIBpos hIB
  set cs := RowCheckCore.ckFx p (prec + 16) with hcs
  set FT := xs.map fun x => RowCheckCore.fI (2 * p.γ) x prec with hFT
  set DT := ds.map fun δ => RowCheckCore.dI p cs δ prec with hDT
  set vs := items.zip vals with hvs
  set Du := RowCheckCore.duOf d DT vs with hDu
  obtain ⟨hDu1, hDu2⟩ := foldl_rmax (fun x : RowCheckCore.VItem =>
    RowCheckCore.duEnt ((DT.getD x.1.e.di default).hi + x.2.2) x.1.D) vs (RowCheckCore.duRad d)
  have hc : (0 : ℝ) < (d : ℝ) / (SR * (1 + ηR)) - ηR := by
    have : (0 : ℝ) < (((d : ℚ) / ((RowCheckCore.S : ℚ) * (1 + RowCheckCore.eta)) -
      RowCheckCore.eta : ℚ) : ℝ) := by exact_mod_cast hd
    push_cast at this
    simpa [SR, ηR] using this
  have hrad : (1 / 6 : ℝ) / ((d : ℝ) / (SR * (1 + ηR)) - ηR) ≤ Du := by
    have := hDu1
    have h' : ((RowCheckCore.duRad d : ℚ) : ℝ) ≤ (Du : ℝ) := by exact_mod_cast this
    simpa [RowCheckCore.duRad, SR, ηR] using h'
  have hDupos : (0 : ℝ) < Du := lt_of_lt_of_le (by positivity) hrad
  have hS := SR_pos
  have hη := ηR_pos
  refine ⟨hg, hLpos, IL, Du, hIB, hDupos, ?_, fun it hit => ?_⟩
  · -- the radius
    have h1 : 1 / 6 / (Du : ℝ) ≤ (d : ℝ) / (SR * (1 + ηR)) - ηR := by
      rw [div_le_iff₀ hDupos]
      rw [div_le_iff₀ hc] at hrad
      linarith
    have h2 : (1 + ηR) * ((d : ℝ) / (SR * (1 + ηR))) = d / SR := by field_simp
    nlinarith
  -- one entry, with the values of its semantics
  obtain ⟨⟨add, exc⟩, hsv, hmem⟩ := mem_zip_of_mapM hvals it hit
  have hsem := specVals_sound hg hsv
  refine ⟨add, exc, hsem, ?_⟩
  have hp := hpre (it, add, exc) hmem
  simp only [RowCheckCore.itemPre, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hD⟩, hdel0⟩, hdel⟩, hdelHi⟩, hxi⟩, hx⟩, hdi⟩, hdd⟩, hdj⟩, hddj⟩, hDlo⟩,
    hFlo⟩ := hp
  have hf := hfeat (it, add, exc) hmem
  simp only [RowCheckCore.itemFeat, decide_eq_true_eq] at hf
  -- the tables
  have hFT : FT.getD it.e.xi default = RowCheckCore.fI (2 * p.γ) (it.e.hi - it.e.anc) prec := by
    rw [hFT, getD_map_of_lt _ 0 hxi, hx]
  have hDTi : DT.getD it.e.di default = RowCheckCore.dI p cs it.e.del prec := by
    rw [hDT, getD_map_of_lt _ 0 hdi, hdd]
  have hDTj : DT.getD it.e.dj default = RowCheckCore.dI p cs it.e.delHi prec := by
    rw [hDT, getD_map_of_lt _ 0 hdj, hddj]
  have hγ : (0 : ℚ) < 2 * p.γ := by have := hg.γ_pos; simp only [ofCore_γ] at this; linarith
  have hFmem := fI_sound hγ (it.e.hi - it.e.anc) prec
  rw [← hFT] at hFmem
  have hDi := dI_sound hg ∅ it.e.del prec
  rw [← hcs, ← hDTi] at hDi
  have hDj := dI_sound hg ∅ it.e.delHi prec
  rw [← hcs, ← hDTj] at hDj
  have hsa : ((ofCore p).s : ℝ) - it.e.anc = ((p.s - it.e.anc : ℚ) : ℝ) := by push_cast; rfl
  -- `D(s - anc)` between `D(delHi)` and `D(del)`
  have hanti1 : ((ofCore p).near ∅).Dδ ((ofCore p).s - it.e.anc) ≤
      ((ofCore p).near ∅).Dδ it.e.del := by
    refine Params.Dδ_anti hg ∅ ?_
    rw [hsa]; exact_mod_cast hdel
  have hanti2 : ((ofCore p).near ∅).Dδ it.e.delHi ≤
      ((ofCore p).near ∅).Dδ ((ofCore p).s - it.e.anc) := by
    refine Params.Dδ_anti hg ∅ ?_
    rw [hsa]; exact_mod_cast hdelHi
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the anchor
    have : (it.e.anc : ℚ) ≤ p.s := by linarith
    simp only [ofCore_s]; exact_mod_cast this
  · -- the feature
    set r : ℚ := (FT.getD it.e.xi default).lo + add - 1 / 6 with hr
    have hr0 : (0 : ℝ) < r := by
      have : (0 : ℚ) < r := by rw [hr]; linarith
      exact_mod_cast this
    have hFr : (r : ℝ) ≤ (laplace (fpar (2 * (p.γ : ℝ))) (((it.e.hi : ℝ) - it.e.anc : ℝ) :
        ℂ)).re + add - 1 / 6 := by
      have := hFmem.1
      push_cast at this
      rw [hr]; push_cast
      linarith
    have hA : 0 < Real.sqrt (IL * Du) := Real.sqrt_pos.2 (mul_pos hILpos hDupos)
    have hsq : ((it.v : ℝ) + SR * ηR) * Real.sqrt (IL * Du) ≤ SR * r := by
      have hf' : (((it.v : ℚ) + (RowCheckCore.S : ℚ) * RowCheckCore.eta) ^ 2 * IL * Du : ℝ) ≤
          ((RowCheckCore.S : ℚ) ^ 2 * r ^ 2 : ℚ) := by exact_mod_cast hf
      push_cast at hf'
      have hv0 : (0 : ℝ) ≤ (it.v : ℝ) + SR * ηR := by
        have : (0 : ℝ) < it.v := by exact_mod_cast hv
        positivity
      rw [← abs_of_nonneg (mul_nonneg hv0 hA.le), ← abs_of_nonneg (mul_nonneg hS.le hr0.le)]
      refine sq_le_sq.1 ?_
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_pos hILpos hDupos).le]
      simpa [SR, ηR, mul_assoc] using hf'
    simp only [ofCore_γ]
    rw [div_le_iff₀ hS]
    have : ((it.v : ℝ) + SR * ηR) ≤ SR * r / Real.sqrt (IL * Du) := by
      rw [le_div_iff₀ hA]; exact hsq
    have h2 : SR * r / Real.sqrt (IL * Du) ≤ SR * (((laplace (fpar (2 * (p.γ : ℝ)))
        (((it.e.hi : ℝ) - it.e.anc : ℝ) : ℂ)).re + add - 1 / 6) / Real.sqrt (IL * Du)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hFr hA.le) hS.le
    nlinarith
  · -- positivity of the diagonal numerator at the true offset
    have := hDj.1
    have h1 : (((1 / 6 : ℚ)) : ℝ) < (DT.getD it.e.dj default).lo := Rat.cast_lt.2 hDlo
    push_cast at h1
    linarith
  · -- the diagonal
    refine ⟨((DT.getD it.e.di default).hi : ℝ) - 1 / 6 + exc, by linarith [hDi.2], ?_⟩
    have hDpos : (0 : ℝ) < it.D := by exact_mod_cast hD
    have hmax := hDu2 (it, add, exc) hmem
    have h' : ((RowCheckCore.duEnt ((DT.getD it.e.di default).hi + exc) it.D : ℚ) : ℝ) ≤ Du := by
      exact_mod_cast hmax
    simp only [RowCheckCore.duEnt] at h'
    push_cast at h'
    rw [div_le_div_iff₀ hDupos hS]
    rw [div_le_iff₀ hDpos] at h'
    simp only [SR, ηR] at h' ⊢
    nlinarith

/-! ## The rows of a leaf -/

lemma mem_of_mapM {α β : Type*} {f : α → Option β} :
    ∀ {l : List α} {out : List β}, l.mapM f = some out → ∀ a ∈ l, ∀ y, f a = some y → y ∈ out
  | [], out, _, a, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, out, h, a, ha, y, hy => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨z, hz, zs, hzs, h⟩ := h
    subst h
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [hy] at hz
      cases hz
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mapM hzs a ha y hy)

lemma mem_filterMap_of_mapM {α β : Type*} {f : α → Option (Option β)} {l : List α}
    {out : List (Option β)} (h : l.mapM f = some out) {a : α} (ha : a ∈ l) {b : β}
    (hb : f a = some (some b)) : b ∈ out.filterMap id :=
  List.mem_filterMap.2 ⟨some b, mem_of_mapM h a ha _ hb, rfl⟩

lemma mapM_some_of_mem {α β : Type*} {f : α → Option β} :
    ∀ {l : List α} {out : List β}, l.mapM f = some out → ∀ a ∈ l, (f a).isSome
  | [], _, _, a, ha => absurd ha List.not_mem_nil
  | x :: l, out, h, a, ha => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, _⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [hy]
    · exact mapM_some_of_mem hys a ha

/-- **An accepted row of a leaf is valid, and its entries cover the columns.** If
`checkRow L k rm = true`, then the row's checked entries `items` satisfy `RowNum`, every family term
of the row has a positive diagonal, and every column `c` with a positive feature in row `k` has a
semantics `e` whose item `⟨v_c, D_c, e⟩` is among the checked entries (as does every family term
with a positive feature and a semantics). -/
theorem checkRow_sound {L : CertCore.Leaf} {k : ℕ} {rm : RowCheckCore.RowMeta} {prec : ℕ}
    (h : RowCheckCore.checkRow L k rm prec = true) :
    ∃ items, RowCheckCore.rowItems L k rm = some items ∧
      RowNum rm.p (L.rows.getD k ⟨1, []⟩).d items ∧
      (∀ t ∈ (L.rows.getD k ⟨1, []⟩).fam, 0 < t.2.2) ∧
      rm.cols.length = L.cols.length ∧ rm.fam.length = (L.rows.getD k ⟨1, []⟩).fam.length ∧
      (∀ c (hc : c < L.cols.length), 0 < (L.cols[c]).v.getD k 0 →
        ∃ e, rm.cols.getD c none = some e ∧
          (⟨(L.cols[c]).v.getD k 0, (L.cols[c]).D.getD k 1, e⟩ : RowCheckCore.Item) ∈ items) ∧
      (∀ i < (L.rows.getD k ⟨1, []⟩).fam.length, ∀ e,
        0 < ((L.rows.getD k ⟨1, []⟩).fam.getD i (0, 0, 0)).2.1 → rm.fam.getD i none = some e →
        (⟨((L.rows.getD k ⟨1, []⟩).fam.getD i (0, 0, 0)).2.1,
          ((L.rows.getD k ⟨1, []⟩).fam.getD i (0, 0, 0)).2.2, e⟩ : RowCheckCore.Item) ∈ items) := by
  unfold RowCheckCore.checkRow at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlc, hlf⟩, hfamD⟩, h⟩ := h
  split at h
  · exact absurd h (by simp)
  rename_i items hitems
  refine ⟨items, hitems, rowCheck_sound h, hfamD, hlc, hlf, ?_, ?_⟩
  · intro c hc hv
    unfold RowCheckCore.rowItems at hitems
    rw [Option.map_eq_some_iff] at hitems
    obtain ⟨cis, hcis, rfl⟩ := hitems
    have hcr : c < rm.cols.length := hlc ▸ hc
    have hmem : ((L.cols[c]), (rm.cols.getD c none)) ∈ L.cols.zip rm.cols := by
      rw [List.getD_eq_getElem _ _ hcr]
      exact List.mem_iff_getElem.2 ⟨c, by rw [List.length_zip]; exact lt_min hc hcr,
        by rw [List.getElem_zip]⟩
    have hsome := mapM_some_of_mem hcis _ hmem
    unfold RowCheckCore.colItem at hsome
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv), Option.isSome_map] at hsome
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨e, he, List.mem_append_left _ ?_⟩
    refine mem_filterMap_of_mapM hcis hmem ?_
    unfold RowCheckCore.colItem
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv), he]
    rfl
  · intro i hi e hv he
    unfold RowCheckCore.rowItems at hitems
    rw [Option.map_eq_some_iff] at hitems
    obtain ⟨cis, _, rfl⟩ := hitems
    have hir : i < rm.fam.length := hlf ▸ hi
    refine List.mem_append_right _ (List.mem_filterMap.2 ⟨(((L.rows.getD k ⟨1, []⟩).fam.getD i
      (0, 0, 0)), (rm.fam.getD i none)), ?_, ?_⟩)
    · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hir]
      exact List.mem_iff_getElem.2 ⟨i, by rw [List.length_zip]; exact lt_min hi hir,
        by rw [List.getElem_zip]⟩
    · show RowCheckCore.famItem _ _ = _
      unfold RowCheckCore.famItem
      rw [ite_eq_left_of_eq_true _ _ (eq_true hv), he]
      rfl

/-- **The rows of an accepted leaf**: every near row with metadata passes `checkRow`. -/
theorem checkRows_sound {L : CertCore.Leaf} {rms : List (Option RowCheckCore.RowMeta)} {prec : ℕ}
    (h : RowCheckCore.checkRows L rms prec = true) :
    rms.length = L.rows.length ∧
      ∀ k < rms.length, ∀ rm, rms.getD k none = some rm → RowCheckCore.checkRow L k rm prec = true := by
  unfold RowCheckCore.checkRows at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun k hk rm hrm => ?_⟩
  have := h.2 k hk
  rw [hrm] at this
  exact this

end GradedNear.Row

end
