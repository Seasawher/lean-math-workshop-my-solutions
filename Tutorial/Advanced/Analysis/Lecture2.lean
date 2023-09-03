import Tutorial.Advanced.Analysis.Lecture1

namespace Tutorial

open scoped Topology Uniformity
open Set Filter 

variable {f : ℝ → ℝ} {f' : ℝ} {x a b : ℝ} 

/-
このファイルの目標は**平均値の定理**の証明である。
-/

/-
まず始めに、極大値を取る点での微分係数はゼロであることの証明をする。定義を確認しておくと、
`f : ℝ → ℝ`が`a : ℝ`で極大値を取るとは、`a`の近傍において`f x ≤ f a`が成り立つことをいう。
-/
example : IsLocalMax f a ↔ ∀ᶠ x in 𝓝 a, f x ≤ f a := .rfl
/-
このように、mathlibでは`a`の近傍において性質`P`が成り立つことを`∀ᶠ x in 𝓝 a, P x`と書く。
これは`ε > 0`を使った次の式と同値となる。
-/
example (P : ℝ → Prop) : (∀ᶠ x in 𝓝 a, P x) ↔ ∃ ε, ε > 0 ∧ ∀ x : ℝ, |x - a| < ε → P x := by
  exact Metric.eventually_nhds_iff
/-
以下の証明では、右側近傍や左側近傍といった概念も用いる。例えば`a`の右側近傍において性質`P`が
成り立つことは`∀ᶠ x in 𝓝[>] a, P x`と表される。もちろんこれも`ε > 0`を使って書き直すこと
ができるが、以下ではmathlibの定理を上手く使うことで`ε > 0`を直接使わないで証明を進める。
-/

/- 
`∀ᶠ x in 𝓝 a, P x`といった記号の正確な意味を理解するには、**フィルター**という概念を知る
必要がある。といっても、以下の演習問題を解く際にはフィルターとは何かを正確に知らなくても
問題ないと思う。近傍`𝓝 a`は直感通りの挙動をするだろう。
-/

/- # 近傍の記号
- `𝓝 a`: `a`の近傍
- `𝓝[>] a` or `𝓝[Ioi a] a`: `a`の右側近傍（`Ioi`はInterval-open-infiniteの略）
- `𝓝[<] a` or `𝓝[Iio a] a`: `a`の左側近傍（`Iio`はInterval-infinite-openの略）
- `𝓝[≠] a` or `𝓝[{a}ᶜ] a`: `a`自身を含まない`a`の近傍（`{a}ᶜ`は`{a}`の補集合）
-/

/-- 極大値を取る点での微分係数はゼロ -/
theorem IsLocalMax.hasDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a) : 
    f' = 0 := by
  -- `f' ≤ 0`と`0 ≤ f'`を示す。
  apply le_antisymm ?right ?left

  -- `f' ≤ 0`を示す
  case right =>
    -- `x`を`a`に右側から近づけたとき`(f x - f a) / (x - a)`は`f`に収束する。
    have hf : Tendsto (fun x ↦ (f x - f a) / (x - a)) (𝓝[>] a) (𝓝 f') := by
      rw [hasDerivAt_iff_tendsto_slope] at hf
      apply hf.mono_left (nhds_right'_le_nhds_ne a)
    -- `(f x - f a) / (x - a)`が`a`の右側近傍で`0`以下であることを示せばよい。
    suffices ∀ᶠ x in 𝓝[>] a, (f x - f a) / (x - a) ≤ 0 from le_of_tendsto hf this
    -- `a`の右側近傍では`a < x`である。
    have ha : ∀ᶠ x in 𝓝[>] a, a < x := eventually_nhdsWithin_of_forall fun x hx ↦ hx
    -- `a`の右側近傍では`f x ≤ f a`である。
    have h : ∀ᶠ x in 𝓝[>] a, f x ≤ f a := h.filter_mono nhdsWithin_le_nhds
    -- 近傍での性質`h₁, ⋯, hₙ`を使って近傍での性質を示したいときは`filter_upwards [h₁, ⋯, hₙ]`を使う。
    filter_upwards [ha, h]
    intro x ha h
    apply div_nonpos_of_nonpos_of_nonneg
    -- 仮定`ha, h`を使って不等式を解く。
    · linarith only [h]
    · linarith only [ha]

  -- `0 ≤ f'`を示す
  case left =>
    -- 右側の場合を真似て証明してみよう。最後は`div_nonneg_of_nonpos`を使うとよい。
    
    -- `x`を`a`に左側から近づけたとき`(f x - f a) / (x - a)`は`f`に収束する
    have hf : Tendsto (fun x ↦ (f x - f a) / (x - a)) (𝓝[<] a) (𝓝 f') := by
      rw [hasDerivAt_iff_tendsto_slope] at hf
      apply hf.mono_left (nhds_left'_le_nhds_ne a)
    
    -- `(f x - f a) / (x - a)`が`a`の左側近傍で`0`以上であることを示せばよい
    suffices ∀ᶠ x in 𝓝[<] a, (f x - f a) / (x - a) ≥ 0 from ge_of_tendsto hf this

    -- `a`の左側近傍では`x < a`である
    have ha : ∀ᶠ x in 𝓝[<] a, x < a := eventually_nhdsWithin_of_forall fun x hx ↦ hx

    -- `a`は極大値なので`f x ≤ f a`である
    have h : ∀ᶠ x in 𝓝[<] a, f x ≤ f a := h.filter_mono nhdsWithin_le_nhds

    -- 近傍での性質`h₁, ⋯, hₙ`を使って近傍での性質を示したいときは`filter_upwards [h₁, ⋯, hₙ]`を使う。
    filter_upwards [ha, h]
    intro x ha h
    apply div_nonneg_of_nonpos
    · linarith only [h]
    · linarith only [ha]

/-- 極小値を取る点での微分係数はゼロ -/
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  -- ヒント: `IsLocalMax.hasDerivAt_eq_zero`を`x ↦ - f x`に対して使おう。
  
  -- `f` を反転させた関数を定義
  set g := fun x => - f x with hdg
  
  -- `g` は `a` で極大値を取る
  have h' : IsLocalMax g a := by
    rw [hdg, IsLocalMax]
    rw [IsLocalMin] at h
    filter_upwards [h]
    simp  

  -- `g` は `a` で微分可能で，微分係数 `- f'` を持つ
  have hg' : HasDerivAt g (- f') a := by
    rw [hdg]
    exact hf.neg

  -- `- f' = 0` を示せばよい
  have : f' = 0 ↔ - f' = 0 := by simp 
  rw [this]

  -- `IsLocalMax.hasDerivAt_eq_zero` を適用する
  apply IsLocalMax.hasDerivAt_eq_zero h' hg'

-- 次の問題で使うかも？
#check IsLocalExtr.elim

/-- 極値を取る点での微分係数はゼロ -/
theorem IsLocalExtr.hasDerivAt_eq_zero (h : IsLocalExtr f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  have h' : IsLocalMax f a ∨ IsLocalMin f a := by exact Iff.mp Or.comm h
  cases h'
  case inl hmax =>
    exact IsLocalMax.hasDerivAt_eq_zero hmax hf
  case inr hmin =>
    exact IsLocalMin.hasDerivAt_eq_zero hmin hf

/-
次の定理はRolleの定理の証明に用いる。
-/

-- 次の問題で使うかも？
#check isCompact_Icc
#check IsCompact.exists_isMaxOn
#check IsCompact.exists_isMinOn

/-- 閉区間上の連続関数は端点において同じ値を持つならば区間の内部で極値を取る。-/
theorem exists_local_extr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c := by

  -- 示すべきことの言い換え
  suffices ∃ c ∈ Ioo a b, IsExtrOn f (Icc a b) c by
    rcases this with ⟨c, cmem, hc⟩
    exists c, cmem
    apply hc.isLocalExtr <| Icc_mem_nhds cmem.1 cmem.2
  
  -- 開区間 `(a, b)` は空ではない
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  
  -- 閉区間 `[a, b]` 上で `f` は最大値をとる
  have ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, IsMaxOn f (Icc a b) C := by
    apply IsCompact.exists_isMaxOn
    exact isCompact_Icc
    exact ne
    exact hfc

  -- 閉区間 `[a, b]` 上で `f` は最小値をとる
  have ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, IsMinOn f (Icc a b) c := by
    apply IsCompact.exists_isMinOn
    exact isCompact_Icc
    exact ne
    exact hfc
  
  change ∀ x ∈ Icc a b, f x ≤ f C at Cge
  change ∀ x ∈ Icc a b, f c ≤ f x at cle
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : ∀ x ∈ Icc a b, f x = f a := fun x hx ↦ le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx ↦ ?_⟩
      simp [this x hx, this c' (Ioo_subset_Icc_self hc')]
    · refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 <| mt ?_ hC, lt_of_le_of_ne Cmem.2 <| mt ?_ hC⟩, Or.inr Cge⟩
      exacts [fun h ↦ by rw [h], fun h ↦ by rw [h, hfI]]
  · refine ⟨c, ⟨lt_of_le_of_ne cmem.1 <| mt ?_ hc, lt_of_le_of_ne cmem.2 <| mt ?_ hc⟩, Or.inl cle⟩
    exacts [fun h ↦ by rw [h], fun h ↦ by rw [h, hfI]]

variable {f f' : ℝ → ℝ} {g g' : ℝ → ℝ} {a b : ℝ} 

/-- Rolleの定理 -/
theorem exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 := by
  
  -- `f` は閉区間 `[a, b]` 上で極値をとる
  have ⟨c, cmem, hc⟩ : ∃ c ∈ Ioo a b, IsLocalExtr f c := by
    apply exists_local_extr_Ioo hab hfc hfI
  
  -- `f' c = 0` を示せばよい
  suffices f' c = 0 by
    exact ⟨c, cmem, this⟩
  
  exact IsLocalExtr.hasDerivAt_eq_zero hc (hff' c cmem)
  
/-- Cauchyの平均値の定理 -/
theorem exists_ratio_hasDerivAt_eq_ratio_slope (hab : a < b) 
    (hfc : ContinuousOn f (Icc a b)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
      (hgc : ContinuousOn g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) :
        ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  
  -- `h` は閉区間 `[a, b]` 上で連続
  have hhc : ContinuousOn h (Icc a b) :=
    (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  
  sorry

-- 次の問題で使うかも？
#check eq_div_iff

/-- Lagrangeの平均値の定理 -/
theorem exists_hasDerivAt_eq_slope (hab : a < b) 
    (hfc : ContinuousOn f (Icc a b)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : 
      ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  sorry

end Tutorial