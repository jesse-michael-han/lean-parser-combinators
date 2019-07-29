import .basic

open parser_tactic

universe u

structure Language : Type (u+1) :=
(functions : ℕ → Type u) (relations : ℕ → Type u)

def Language.constants (L : Language) := L.functions 0

variable (L : Language.{u})

inductive preterm : ℕ → Type u
| var {} : ∀ (k : ℕ), preterm 0
| func : ∀ {l : ℕ} (f : L.functions l), preterm l
| app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l
export preterm

@[reducible] def term := preterm L 0

variable {L}
prefix `&`:max := preterm.var

-- @[simp] def apps : ∀{l}, preterm L l → dvector (term L) l → term L
-- | _ t []       := t
-- | _ t (t'::ts) := apps (app t t') ts

-- -- @[simp] def apps' : ∀{l l'}, preterm L (l'+l) → dvector (term L) l → preterm L l'
-- -- | _ _ t []       := t
-- -- | _ _ t (t'::ts) := apps' (app t t') ts

-- -- @[simp] def rev_apps : ∀{l l'}, preterm L (l+l) → dvector (term L) l' → preterm L l
-- -- | _ _ t []       := sorry
-- -- | l _ t (@dvector.cons _ l' t' ts) := app (@rev_apps (l+1) l' t ts) t'

-- @[simp] lemma apps_zero (t : term L) (ts : dvector (term L) 0) : apps t ts = t :=
-- by cases ts; refl

-- lemma apps_eq_app {l} (t : preterm L (l+1)) (s : term L) (ts : dvector (term L) l) :
--   ∃t' s', apps t (s::ts) = app t' s' :=
-- begin
--   induction ts generalizing s, exact ⟨t, s, rfl⟩, exact ts_ih (app t s) ts_x
-- end

-- namespace preterm
-- @[simp] def change_arity' : ∀{l l'} (h : l = l') (t : preterm L l), preterm L l'
-- | _ _ h &k          := by induction h; exact &k
-- | _ _ h (func f)    := func (by induction h; exact f)
-- | _ _ h (app t₁ t₂) := app (change_arity' (congr_arg succ h) t₁) t₂

-- @[simp] lemma change_arity'_rfl : ∀{l} (t : preterm L l), change_arity' rfl t = t
-- | _ &k          := by refl
-- | _ (func f)    := by refl
-- | _ (app t₁ t₂) := by dsimp; simp*

-- end preterm

-- -- lemma apps'_concat {l l'} (t : preterm L (l'+(l+1))) (s : term L) (ts : dvector (term L) l) :
-- --   apps' t (ts.concat s) = app (apps' (t.change_arity' (by simp)) ts) s :=
-- -- begin
-- --   induction ts generalizing s,
-- --   { simp },
-- --   { apply ts_ih (app t ts_x) s }
-- -- end

-- lemma apps_ne_var {l} {f : L.functions l} {ts : dvector (term L) l} {k : ℕ} :
--   apps (func f) ts ≠ &k :=
-- begin
--   intro h, cases ts, injection h,
--   rcases apps_eq_app (func f) ts_x ts_xs with ⟨t, s, h'⟩, cases h.symm.trans h'
-- end

-- lemma apps_inj' {l} {t t' : preterm L l} {ts ts' : dvector (term L) l}
--   (h : apps t ts = apps t' ts') : t = t' ∧ ts = ts' :=
-- begin
--   induction ts; cases ts',
--   { exact ⟨h, rfl⟩ },
--   { rcases ts_ih h with ⟨⟨rfl, rfl⟩, rfl⟩, exact ⟨rfl, rfl⟩ }
-- end

-- -- lemma apps_inj_length {l l'} {f : L.functions l} {f' : L.functions l'}
-- --   {ts : dvector (term L) l} {ts' : dvector (term L) l'}
-- --   (h : apps (func f) ts = apps (func f') ts') : l = l' :=
-- -- begin
-- --   sorry
-- -- end

-- -- lemma apps'_inj_length {l₁ l₂ l'} {f : L.functions (l' + l₁)} {f' : L.functions (l' + l₂)}
-- --   {ts : dvector (term L) l₁} {ts' : dvector (term L) l₂}
-- --   (h : apps' (func f) ts = apps' (func f') ts') : l₁ = l₂ :=
-- -- begin
-- --   sorry
-- --   -- induction ts generalizing l'; cases ts',
-- --   -- { refl },
-- --   -- { rcases apps'_eq_app (func f') ts'_x ts'_xs with ⟨t, s, h'⟩, cases h.trans h' },
-- --   -- { rcases apps'_eq_app (func f) ts_x ts_xs with ⟨t, s, h'⟩, cases h.symm.trans h' },
-- --   -- { rcases apps'_eq_app (func f) ts_x ts_xs with ⟨t₁, s₁, h₁⟩,
-- --   --   rcases apps'_eq_app (func f') ts'_x ts'_xs with ⟨t₂, s₂, h₂⟩,
-- --   --    }
-- -- end

-- lemma apps_inj {l} {f f' : L.functions l} {ts ts' : dvector (term L) l}
--   (h : apps (func f) ts = apps (func f') ts') : f = f' ∧ ts = ts' :=
-- by rcases apps_inj' h with ⟨h', rfl⟩; cases h'; exact ⟨rfl, rfl⟩

-- def term_of_function {l} (f : L.functions l) : arity' (term L) (term L) l :=
-- arity'.of_dvector_map $ apps (func f)

-- @[elab_as_eliminator] def term.rec {C : term L → Sort v}
--   (hvar : ∀(k : ℕ), C &k)
--   (hfunc : Π {l} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : ∀t, ts.pmem t → C t),
--     C (apps (func f) ts)) : ∀(t : term L), C t :=
-- have h : ∀{l} (t : preterm L l) (ts : dvector (term L) l) (ih_ts : ∀s, ts.pmem s → C s),
--   C (apps t ts),
-- begin
--   intros, induction t; try {rw ts.zero_eq},
--   { apply hvar },
--   { apply hfunc t_f ts ih_ts },
--   { apply t_ih_t (t_s::ts), intros t ht,
--     cases ht,
--     { induction ht, apply t_ih_s ([]), intros s hs, cases hs },
--     { exact ih_ts t ht }},
-- end,
-- λt, h t ([]) (by intros s hs; cases hs)

-- @[elab_as_eliminator] def term.elim' {C : Type v}
--   (hvar : ∀(k : ℕ), C)
--   (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C) :
--   ∀{l} (t : preterm L l) (ts : dvector (term L) l) (ih_ts : dvector C l), C
-- | _ &k ts ih_ts        := hvar k
-- | _ (func f) ts ih_ts  := hfunc f ts ih_ts
-- | _ (app t s) ts ih_ts := term.elim' t (s::ts) (term.elim' s ([]) ([])::ih_ts)

-- @[elab_as_eliminator] def term.elim {C : Type v}
--   (hvar : ∀(k : ℕ), C)
--   (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C) :
--   ∀(t : term L), C :=
-- λt, term.elim' hvar hfunc t ([]) ([])

-- lemma term.elim'_apps {C : Type v}
--   (hvar : ∀(k : ℕ), C)
--   (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C)
--   {l} (t : preterm L l) (ts : dvector (term L) l) :
--   @term.elim' L C hvar hfunc 0 (apps t ts) ([]) ([]) = @term.elim' L C hvar hfunc l t ts
--   (ts.map $ term.elim hvar hfunc) :=
-- begin
--   induction ts,
--   { refl },
--   { dsimp only [dvector.map, apps], rw [ts_ih], refl }
-- end

-- lemma term.elim_apps {C : Type v}
--   (hvar : ∀(k : ℕ), C)
--   (hfunc : Π {{l}} (f : L.functions l) (ts : dvector (term L) l) (ih_ts : dvector C l), C)
--   {l} (f : L.functions l) (ts : dvector (term L) l) :
--   @term.elim L C hvar hfunc (apps (func f) ts) = hfunc f ts (ts.map $ @term.elim L C hvar hfunc) :=
-- by dsimp only [term.elim]; rw term.elim'_apps; refl

-- /- lift_term_at _ t n m raises variables in t which are at least m by n -/
-- @[simp] def lift_term_at : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
-- | _ &k          n m := &(if m ≤ k then k+n else k)
-- | _ (func f)    n m := func f
-- | _ (app t₁ t₂) n m := app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

-- notation t ` ↑' `:90 n ` # `:90 m:90 := fol.lift_term_at t n m -- input ↑ with \u or \upa

-- -- @[simp] lemma lift_term_var_le {k n m} (h : m ≤ k) : &k ↑' n # m = (&(k+n) : term L) := dif_pos h
-- -- @[simp] lemma lift_term_var_gt {k n m} (h : ¬(m ≤ k)) : &k ↑' n # m = (&k : term L) := dif_neg h
-- -- @[simp] lemma lift_term_at_func {l} (f : L.functions l) (n m) : func f ↑' n # m = func f := by refl
-- -- @[simp] lemma lift_term_at_app {l} (t : preterm L (l+1)) (s : preterm L 0) (n m) :
-- --   app t s ↑' n # m = app (t ↑' n # m) (s ↑' n # m) := by refl

-- @[reducible] def lift_term {l} (t : preterm L l) (n : ℕ) : preterm L l := t ↑' n # 0
-- infix ` ↑ `:100 := fol.lift_term -- input ↑' with \u or \upa
-- @[reducible, simp] def lift_term1 {l} (t : preterm L l) : preterm L l := t ↑ 1

-- @[simp] lemma lift_term_def {l} (t : preterm L l) (n : ℕ) : t ↑' n # 0 = t ↑ n := by refl

-- lemma injective_lift_term_at : ∀ {l} {n m : ℕ},
--   function.injective (λ(t : preterm L l), lift_term_at t n m)
-- | _ n m &k &k' h :=
--   by by_cases h₁ : m ≤ k; by_cases h₂ : m ≤ k'; simp [h₁, h₂] at h;
--      congr;[assumption, skip, skip, assumption]; exfalso; try {apply h₁};
--      try {apply h₂}; subst h; apply le_trans (by assumption) (le_add_left _ _)
-- | _ n m &k (func f')            h := by cases h
-- | _ n m &k (app t₁' t₂')        h := by cases h
-- | _ n m (func f) &k'            h := by cases h
-- | _ n m (func f) (func f')      h := h
-- | _ n m (func f) (app t₁' t₂')  h := by cases h
-- | _ n m (app t₁ t₂) &k'         h := by cases h
-- | _ n m (app t₁ t₂) (func f')   h := by cases h
-- | _ n m (app t₁ t₂) (app t₁' t₂') h :=
--   begin injection h, congr; apply injective_lift_term_at; assumption end

-- @[simp] lemma lift_term_at_zero : ∀ {l} (t : preterm L l) (m : ℕ), t ↑' 0 # m = t
-- | _ &k          m := by simp [lift_term_at]
-- | _ (func f)    m := by refl
-- | _ (app t₁ t₂) m := by dsimp; congr; apply lift_term_at_zero

-- @[simp] lemma lift_term_zero {l} (t : preterm L l) : t ↑ 0 = t := lift_term_at_zero t 0

-- /- the following lemmas simplify iterated lifts, depending on the size of m' -/
-- lemma lift_term_at2_small : ∀ {l} (t : preterm L l) (n n') {m m'}, m' ≤ m →
--   (t ↑' n # m) ↑' n' # m' = (t ↑' n' # m') ↑' n # (m + n')
-- | _ &k          n n' m m' H :=
--   begin
--     by_cases h : m ≤ k,
--     { have h₁ : m' ≤ k := le_trans H h,
--       have h₂ : m' ≤ k + n, from le_trans h₁ (k.le_add_right n),
--       simp [*, -add_assoc, -add_comm], simp },
--     { have h₁ : ¬m + n' ≤ k + n', from λ h', h (le_of_add_le_add_right h'),
--       have h₂ : ¬m + n' ≤ k, from λ h', h₁ (le_trans h' (k.le_add_right n')),
--       by_cases h' : m' ≤ k; simp [*, -add_comm, -add_assoc] }
--   end
-- | _ (func f)    n n' m m' H := by refl
-- | _ (app t₁ t₂) n n' m m' H :=
--   begin dsimp; congr1; apply lift_term_at2_small; assumption end

-- lemma lift_term_at2_medium : ∀ {l} (t : preterm L l) {n} (n') {m m'}, m ≤ m' → m' ≤ m+n →
--   (t ↑' n # m) ↑' n' # m' = t ↑' (n+n') # m
-- | _ &k          n n' m m' H₁ H₂ :=
--   begin
--     by_cases h : m ≤ k,
--     { have h₁ : m' ≤ k + n, from le_trans H₂ (add_le_add_right h n), simp [*, -add_comm], },
--     { have h₁ : ¬m' ≤ k, from λ h', h (le_trans H₁ h'), simp [*, -add_comm, -add_assoc] }
--   end
-- | _ (func f)    n n' m m' H₁ H₂ := by refl
-- | _ (app t₁ t₂) n n' m m' H₁ H₂ :=
--   begin dsimp; congr1; apply lift_term_at2_medium; assumption end

-- lemma lift_term2_medium {l} (t : preterm L l) {n} (n') {m'} (h : m' ≤ n) :
--   (t ↑ n) ↑' n' # m' = t ↑ (n+n') :=
-- lift_term_at2_medium t n' m'.zero_le (by simp*)

-- lemma lift_term2 {l} (t : preterm L l) (n n') : (t ↑ n) ↑ n' = t ↑ (n+n') :=
-- lift_term2_medium t n' n.zero_le

-- lemma lift_term_at2_eq {l} (t : preterm L l) (n n' m : ℕ) :
--   (t ↑' n # m) ↑' n' # (m+n) = t ↑' (n+n') # m :=
-- lift_term_at2_medium t n' (m.le_add_right n) (le_refl _)

-- lemma lift_term_at2_large {l} (t : preterm L l) {n} (n') {m m'} (H : m + n ≤ m') :
--   (t ↑' n # m) ↑' n' # m' = (t ↑' n' # (m'-n)) ↑' n # m :=
-- have H₁ : n ≤ m', from le_trans (n.le_add_left m) H,
-- have H₂ : m ≤ m' - n, from nat.le_sub_right_of_add_le H,
-- begin rw fol.lift_term_at2_small t n' n H₂, rw [nat.sub_add_cancel], exact H₁ end

-- @[simp] lemma lift_term_var0 (n : ℕ) : &0 ↑ n = (&n : term L) :=
-- by have h : 0 ≤ 0 := le_refl 0; rw [←lift_term_def]; simp [h, -lift_term_def]

-- @[simp] lemma lift_term_at_apps {l} (t : preterm L l) (ts : dvector (term L) l) (n m : ℕ) :
--   (apps t ts) ↑' n # m = apps (t ↑' n # m) (ts.map $ λx, x ↑' n # m) :=
-- by induction ts generalizing t;[refl, apply ts_ih (app t ts_x)]

-- @[simp] lemma lift_term_apps {l} (t : preterm L l) (ts : dvector (term L) l) (n : ℕ) :
--   (apps t ts) ↑ n = apps (t ↑ n) (ts.map $ λx, x ↑ n) :=
-- lift_term_at_apps t ts n 0

-- /- subst_term t s n substitutes s for (&n) and reduces the level of all variables above n by 1 -/
-- def subst_term : ∀ {l}, preterm L l → term L → ℕ → preterm L l
-- | _ &k          s n := subst_realize var (s ↑ n) n k
-- | _ (func f)    s n := func f
-- | _ (app t₁ t₂) s n := app (subst_term t₁ s n) (subst_term t₂ s n)

-- notation t `[`:max s ` // `:95 n `]`:0 := fol.subst_term t s n

-- @[simp] lemma subst_term_var_lt (s : term L) {k n : ℕ} (H : k < n) : &k[s // n] = &k :=
-- by simp only [H, fol.subst_term, fol.subst_realize_lt, eq_self_iff_true]

-- @[simp] lemma subst_term_var_gt (s : term L) {k n : ℕ} (H : n < k) : &k[s // n] = &(k-1) :=
-- by simp only [H, fol.subst_term, fol.subst_realize_gt, eq_self_iff_true]

-- @[simp] lemma subst_term_var_eq (s : term L) (n : ℕ) : &n[s // n] = s ↑' n # 0 :=
-- by simp [subst_term]

-- lemma subst_term_var0 (s : term L) : &0[s // 0] = s := by simp

-- @[simp] lemma subst_term_func {l} (f : L.functions l) (s : term L) (n : ℕ) :
--   (func f)[s // n] = func f :=
-- by refl

-- @[simp] lemma subst_term_app {l} (t₁ : preterm L (l+1)) (t₂ s : term L) (n : ℕ) :
--   (app t₁ t₂)[s // n] = app (t₁[s // n]) (t₂[s // n]) :=
-- by refl

-- @[simp] lemma subst_term_apps {l} (t : preterm L l) (ts : dvector (term L) l) (s : term L)
--   (n : ℕ) : (apps t ts)[s // n] = apps (t[s // n]) (ts.map $ λx, x[s // n]) :=
-- by induction ts generalizing t;[refl, apply ts_ih (app t ts_x)]

-- /- the following lemmas simplify first lifting and then substituting, depending on the size
--   of the substituted variable -/
-- lemma lift_at_subst_term_large : ∀{l} (t : preterm L l) (s : term L) {n₁} (n₂) {m}, m ≤ n₁ →
--  (t ↑' n₂ # m)[s // n₁+n₂] = (t [s // n₁]) ↑' n₂ # m
-- | _ &k          s n₁ n₂ m h :=
--   begin
--     apply decidable.lt_by_cases k n₁; intro h₂,
--     { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (by simp*),
--       by_cases m ≤ k; simp* },
--     { subst h₂, simp [*, lift_term2_medium] },
--     { have h₂ : m < k, by apply lt_of_le_of_lt; assumption,
--       have : m ≤ k - 1, from nat.le_sub_right_of_add_le (succ_le_of_lt h₂),
--       have : m ≤ k, from le_of_lt h₂,
--       have : 1 ≤ k, from one_le_of_lt h₂,
--       simp [*, nat.add_sub_swap this n₂, -add_assoc, -add_comm] }
--   end
-- | _ (func f)    s n₁ n₂ m h := rfl
-- | _ (app t₁ t₂) s n₁ n₂ m h := by simp*

-- lemma lift_subst_term_large {l} (t : preterm L l) (s : term L) (n₁ n₂) :
--   (t ↑ n₂)[s // n₁+n₂] = (t [s // n₁]) ↑ n₂ :=
-- lift_at_subst_term_large t s n₂ n₁.zero_le

-- lemma lift_subst_term_large' {l} (t : preterm L l) (s : term L) (n₁ n₂) :
--   (t ↑ n₂)[s // n₂+n₁] = (t [s // n₁]) ↑ n₂ :=
-- by rw [add_comm]; apply lift_subst_term_large

-- lemma lift_at_subst_term_medium : ∀{l} (t : preterm L l) (s : term L) {n₁ n₂ m}, m ≤ n₂ →
--   n₂ ≤ m + n₁ → (t ↑' n₁+1 # m)[s // n₂] = t ↑' n₁ # m
-- | _ &k          s n₁ n₂ m h₁ h₂ :=
--   begin
--     by_cases h : m ≤ k,
--     { have h₃ : n₂ < k + (n₁ + 1), from lt_succ_of_le (le_trans h₂ (add_le_add_right h _)),
--       simp [*, add_sub_cancel_right] },
--     { have h₃ : k < n₂, from lt_of_lt_of_le (lt_of_not_ge h) h₁, simp* }
--   end
-- | _ (func f)    s n₁ n₂ m h₁ h₂ := rfl
-- | _ (app t₁ t₂) s n₁ n₂ m h₁ h₂ := by simp*

-- lemma lift_subst_term_medium {l} (t : preterm L l) (s : term L) (n₁ n₂) :
--   (t ↑ ((n₁ + n₂) + 1))[s // n₁] = t ↑ (n₁ + n₂) :=
-- lift_at_subst_term_medium t s n₁.zero_le (by rw [zero_add]; exact n₁.le_add_right n₂)

-- lemma lift_at_subst_term_eq {l} (t : preterm L l) (s : term L) (n : ℕ) : (t ↑' 1 # n)[s // n] = t :=
-- begin rw [lift_at_subst_term_medium t s, lift_term_at_zero]; refl end

-- @[simp] lemma lift_term1_subst_term {l} (t : preterm L l) (s : term L) : (t ↑ 1)[s // 0] = t :=
-- lift_at_subst_term_eq t s 0

-- lemma lift_at_subst_term_small : ∀{l} (t : preterm L l) (s : term L) (n₁ n₂ m),
--  (t ↑' n₁ # (m + n₂ + 1))[s ↑' n₁ # m // n₂] = (t [s // n₂]) ↑' n₁ # (m + n₂)
-- | _ &k          s n₁ n₂ m :=
--   begin
--     by_cases h : m + n₂ + 1 ≤ k,
--     { change m + n₂ + 1 ≤ k at h,
--       have h₂ : n₂ < k := lt_of_le_of_lt (le_add_left n₂ m) (lt_of_succ_le h),
--       have h₃ : n₂ < k + n₁ := by apply nat.lt_add_right; exact h₂,
--       have h₄ : m + n₂ ≤ k - 1 := nat.le_sub_right_of_add_le h,
--       simp [*, -add_comm, -add_assoc, nat.add_sub_swap (one_le_of_lt h₂)] },
--     { change ¬(m + n₂ + 1 ≤ k) at h,
--       apply decidable.lt_by_cases k n₂; intro h₂,
--       { have h₃ : ¬(m + n₂ ≤ k) := λh', not_le_of_gt h₂ (le_trans (le_add_left n₂ m) h'),
--         simp [h, h₂, h₃, -add_comm, -add_assoc] },
--       { subst h₂,
--         have h₃ : ¬(k + m + 1 ≤ k) := by rw [add_comm k m]; exact h,
--         simp [h, h₃, -add_comm, -add_assoc],
--         exact lift_term_at2_small _ _ _ m.zero_le },
--       { have h₃ : ¬(m + n₂ ≤ k - 1) :=
--           λh', h $ (nat.le_sub_right_iff_add_le $ one_le_of_lt h₂).mp h',
--         simp [h, h₂, h₃, -add_comm, -add_assoc] }}
--   end
-- | _ (func f)    s n₁ n₂ m := rfl
-- | _ (app t₁ t₂) s n₁ n₂ m := by simp [*, -add_assoc, -add_comm]

-- lemma subst_term2 : ∀{l} (t : preterm L l) (s₁ s₂ : term L) (n₁ n₂),
--   t [s₁ // n₁] [s₂ // n₁ + n₂] = t [s₂ // n₁ + n₂ + 1] [s₁[s₂ // n₂] // n₁]
-- | _ &k          s₁ s₂ n₁ n₂ :=
--   begin -- can we use subst_realize2 here?
--     apply decidable.lt_by_cases k n₁; intro h,
--     { have : k < n₁ + n₂, from lt_of_le_of_lt (k.le_add_right n₂) (by simp*),
--       have : k < n₁ + n₂ + 1, from lt.step this,
--       simp only [*, eq_self_iff_true, fol.subst_term_var_lt] },
--     { have : k < k + (n₂ + 1), from lt_succ_of_le (le_add_right _ n₂),
--       subst h, simp [*, lift_subst_term_large', -add_comm] },
--     apply decidable.lt_by_cases k (n₁ + n₂ + 1); intro h',
--     { have : k - 1 < n₁ + n₂, from (nat.sub_lt_right_iff_lt_add (one_le_of_lt h)).2 h',
--       simp [*, -add_comm, -add_assoc] },
--     { subst h', simp [h, lift_subst_term_medium, -add_comm, -add_assoc] },
--     { have : n₁ + n₂ < k - 1, from nat.lt_sub_right_of_add_lt h',
--       have : n₁ < k - 1, from lt_of_le_of_lt (n₁.le_add_right n₂) this,
--       simp only [*, eq_self_iff_true, fol.subst_term_var_gt] }
--   end
-- | _ (func f)    s₁ s₂ n₁ n₂ := rfl
-- | _ (app t₁ t₂) s₁ s₂ n₁ n₂ := by simp*

-- lemma subst_term2_0 {l} (t : preterm L l) (s₁ s₂ : term L) (n) :
--   t [s₁ // 0] [s₂ // n] = t [s₂ // n + 1] [s₁[s₂ // n] // 0] :=
-- let h := subst_term2 t s₁ s₂ 0 n in by simp only [zero_add] at h; exact h

-- lemma lift_subst_term_cancel : ∀{l} (t : preterm L l) (n : ℕ), (t ↑' 1 # (n+1))[&0 // n] = t
-- | _ &k          n :=
--   begin
--     apply decidable.lt_by_cases n k; intro h,
--     { change n+1 ≤ k at h, have h' : n < k+1, from lt.step (lt_of_succ_le h), simp [h, h'] },
--     { have h' : ¬(k+1 ≤ k), from not_succ_le_self k, simp [h, h'] },
--     { have h' : ¬(n+1 ≤ k) := not_le_of_lt (lt.step h), simp [h, h'] }
--   end
-- | _ (func f)    n := rfl
-- | _ (app t₁ t₂) n := by dsimp; simp [*]


-- /- Probably useful facts about substitution which we should add when needed:
-- (forall M N i j k, ( M [ j ← N] ) ↑' k # (j+i) = (M ↑' k # (S (j+i))) [ j ← (N ↑' k # i ) ])
-- subst_travers : (forall M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]])
-- erasure_lem3 : (forall n m t, m>n->#m = (#m ↑' 1 # (S n)) [n ← t]).
-- lift_is_lift_sublemma : forall j v, j<v->exists w,#v=w↑1#j.
-- lift_is_lift : (forall N A n i j,N ↑' i # n=A ↑' 1 # j -> j<n -> exists M,N=M ↑' 1 # j)
-- subst_is_lift : (forall N T A n j, N [n ← T]=A↑' 1#j->j<n->exists M,N=M↑' 1#j)
-- -/

-- /- preformula l is a partially applied formula. if applied to n terms, it becomes a formula.
--   * We only have implication as binary connective. Since we use classical logic, we can define
--     the other connectives from implication and falsum.
--   * Similarly, universal quantification is our only quantifier.
--   * We could make `falsum` and `equal` into elements of rel. However, if we do that, then we cannot make the interpretation of them in a model definitionally what we want.
-- -/
variable (L)
inductive preformula : ℕ → Type u
| falsum {} : preformula 0
| equal (t₁ t₂ : term L) : preformula 0
| rel {l : ℕ} (R : L.relations l) : preformula l
| apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
| imp (f₁ f₂ : preformula 0) : preformula 0
| all (f : preformula 0) : preformula 0
export preformula
@[reducible] def formula := preformula L 0
variable {L}

notation `⊥` := preformula.falsum -- input: \bot
infix ` ≃ `:88 := preformula.equal -- input \~- or \simeq
infixr ` ⟹ `:62 := preformula.imp -- input \==>
prefix `∀'`:110 := preformula.all
def preformula.not   (f : formula L)     : formula L := f ⟹ ⊥
prefix `∼`:max := preformula.not -- input \~, the ASCII character ~ has too low precedence
notation `⊤` := ∼⊥ -- input: \top
def preformula.and   (f₁ f₂ : formula L) : formula L := ∼(f₁ ⟹ ∼f₂)
infixr ` ⊓ ` := preformula.and -- input: \sqcap
def preformula.or    (f₁ f₂ : formula L) : formula L := ∼f₁ ⟹ f₂
infixr ` ⊔ ` := preformula.or -- input: \sqcup
def biimp (f₁ f₂ : formula L) : formula L := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
infix ` ⇔ `:61 := biimp -- input \<=>
def ex    (f : formula L)     : formula L := ∼ ∀' ∼f
prefix `∃'`:110 := ex -- input \ex

meta instance preterm.reflect {L : Language.{0}} [reflected L] [∀ n, has_reflect (L.functions n)] :
  ∀{n}, has_reflect (preterm L n)
| _ &k          := `(&k)
| _ (func f)    := `(func f)
| _ (app t₁ t₂) := (`(λ x y, app x y).subst (preterm.reflect t₁)).subst (preterm.reflect t₂)

meta instance preformula.reflect {L : Language.{0}} [reflected L] [∀ n, has_reflect (L.functions n)]
  [∀ n, has_reflect (L.relations n)] : ∀{n}, has_reflect (preformula L n)
| _ falsum           := `(falsum)
| _ (equal t₁ t₂)    := (`(λ x₁ x₂, equal x₁ x₂).subst (preterm.reflect t₁)).subst (preterm.reflect t₂)
| _ (rel R)          := `(λ x, preformula.rel x).subst `(R)
| _ (apprel f t)     := (`(λ x₁ x₂, apprel x₁ x₂).subst (preformula.reflect f)).subst (preterm.reflect t)
| _ (imp f₁ f₂)      := (`(λ x₁ x₂, imp x₁ x₂).subst (preformula.reflect f₁)).subst (preformula.reflect f₂)
| _ (all f)          := `(λ x, all x).subst (preformula.reflect f)

def L_empty : Language :=
  ⟨λ _, empty, λ _, empty⟩

meta instance L_empty.reflect_functions : ∀ n, has_reflect (L_empty.functions n) :=
λ _ _, empty.elim ‹_›

meta instance L_empty.reflect_relations : ∀ n, has_reflect (L_empty.relations n) :=
λ _ _, empty.elim ‹_›

meta def parse_preterm : Π {k}, parser_tactic $ preterm L_empty k
| 0 := alphanumeric_token *> return (preterm.var 0)
| (n+1) := fail

meta def parse_term := @parse_preterm 0

-- -- note(jesse): for non-empty languages, need parsers parametrized over the function and relation symbols
-- meta def parse_preformula : Π {k},  parser_tactic $ preformula L_empty k
-- | 0 := (-- preformula.all <$> ((token $ str "∀") *> @parse_preformula 0) <|> 
-- do b <- lookahead "⟹",
--           if b then preformula.imp <$> (@parse_preformula 0) <*>(@parse_preformula 0)
--                else fail <|>
--        (token $ str "⊥") *> return preformula.falsum <|>
--        preformula.equal <$> @parse_preterm 0 <* (token $ str "=") <*> @parse_preterm 0) <* whitespace -- TODO(jesse) eliminate the recursive call
-- | (n+1) := fail

-- meta def parse_formula := @parse_preformula 0

-- a ⟹ (b ⟹ (c ⟹ d)) -- let's assume that implication associates to the right

-- gets parsed as
-- app "imp" [leaf "a", app "imp" [leaf "b", app "imp" ["leaf c", leaf "d"]]]

inductive tree (α : Type) : Type
| leaf (a : α) : tree
| app (l : option α) (ts : list tree) : tree
open tree

def add_subtree {α} : ∀ (t : tree α) (t' : tree α), tree α
| (leaf a) t' := app none [t', leaf a]
| (app l ts) t' := app l $ t' :: ts

def add_parent {α} : ∀ (t : tree α) (a : option α), tree α :=
λ t a, app a [t]

def imp_handler (arg : string) (t : tree string) : tree string :=
if arg = "⟹" then add_parent t (some arg) else add_subtree t (leaf arg)

-- meta def parse_imp_aux : tree string → (parser_tactic $ tree string) :=
-- λ t, do
--   imp_handler <$> return t <*> (token $ not_whitespace)

meta def parse_imp : (parser_tactic $ tree string) :=
do  x <- token not_whitespace,
    (imp_handler <$> return x <*> parse_imp) <|> return (leaf x)

meta instance tree_string_reflect : has_reflect (tree string)
| (leaf arg) := `(λ x, leaf x).subst `(arg)
| (app l ts) := (`(λ x y, tree.app x y).subst `(l)).subst (by haveI := tree_string_reflect; exact list.reflect ts)
  
def my_tree' : tree string := by (parse_imp).get_result "a ⟹ b ⟹ c ⟹ d"

#print my_tree'

-- def my_eq : preformula L_empty 0 := by (preformula.equal <$> @parse_preterm 0 <* (token $ str "=") <*> @parse_preterm 0).get_result "a = a"

-- def my_falsum : preformula L_empty 0 := by parse_formula.get_result "a = a ⟹ a = b"

-- #reduce my_falsum

-- def foo := by (preformula.all <$> (symb "∀" *> eof)).get_result "∀"

-- #reduce my_eq -- &0 ≃ &0
       
-- def foo : preterm L_empty 0 := by parse_term.get_result "f1"

-- #reduce by parse_term.get_result "f1"

-- run_cmd (run' (preformula.all <$> (str "∀" *> @parse_preformula 0)) "foo"

-- def my_falsum : preformula L_empty 0 := by parse_formula.get_result "⊥"

-- #reduce by parse_term.get_result ""

-- #eval by (token $ str "=").get_result "="

-- #reduce "foo"
