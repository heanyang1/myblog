---
layout: post
title:  "Type Safety Proof (Part 3)"
---

> This is the third post of a series about implementing and proving a HM type inference system. Here's the [previous post](/myblog/2026/05/17/rewriting-interpreter-in-haskell.html).
>
> Edited on 6/7: the agent-coding mess is cleaned up. The proof should be correct, but I don't have enough brain power to read it. I'll update again when I fully understand the proof.
>
> Edited on 6/13: I think get the overall idea of the proof. This should be the end of updating this post.

I'm trying to use an AI agent to write the type safety proof for [my interpreter](https://github.com/heanyang1/interpreter) in [Lean 4](https://lean-lang.org). Here's the progress so far.

## De Bruijn Indexes in Evaluation

I switched to de Bruijn indexes in type checking, so the evaluation should also be using de Bruijn indexes for consistency.

The substitution rule of de Bruijn indexes described on [Wikipedia](https://en.wikipedia.org/wiki/De_Bruijn_index) considers the cases where there are free variables, which makes the rule unnecessarily complex. Since no free variable is allowed in evaluation, the process can be simplified.

We will change the D-App-Sub rule
\[\frac{}{(\lambda (x:\tau)\, .\, e_{\mathsf{lam}})\,e_{\mathsf{arg}}\mapsto[x\to e_{\mathsf{arg}}]\,e_{\mathsf{lam}}}\]
into
\[\frac{}{(\lambda \_\, .\, e_{\mathsf{lam}})\,e_{\mathsf{arg}}\mapsto[\left<0\right>\to e_{\mathsf{arg}}]_D\,e_{\mathsf{lam}}},\]
where \([\cdot]_D\) is defined as
\[\begin{aligned}
    [\left<n\right>\to e]_D\left<n\right> & =e, \\
    [\left<n\right>\to e]_D\left<k\right> & =\left<k\right>, & (k\neq n) \\
    [\left<n\right>\to e]_D(e_1\oplus e_2) & =([\left<n\right>\to e]_D\, e_1)\oplus ([\left<n\right>\to e]_D\, e_2), \\
    [\left<n\right>\to e]_D(\lambda \_\, .\, e_1) & =\lambda \_\, .\, ([\left<n+1\right>\to e]_D\, e_1) \\
\end{aligned}\]
and so on. The full definition is given as the `deBruijnSubst` function.

## Setup and Run

After a few attempts, I'm convinced that the free-tier agents are not capable enough to write Lean 4 code, so I bought some tokens from [DeepSeek](https://www.deepseek.com/) to use their pro model, added [Lean 4 skills](https://github.com/cameronfreer/lean4-skills) and [Lean LSP MCP](https://github.com/oOo0oOo/lean-lsp-mcp) to OpenCode. Now the agent seems to have no trouble writing Lean code.

After burning 100M tokens (which costs about 8.5￥) and a few hours of running, the agent produced the proof in a 900-line file and confidently say that it's completed.

The last two theorems are indeed the type safety theorems we wanted:
{% highlight lean %}
theorem progress (e : Expr) (τ : Ty) (h : Typing emptyCtx e τ) : Value e ∨ ∃ e', Step e e' := by
    -- ...
theorem preservation (e e' : Expr) (τ : Ty) (h : Typing emptyCtx e τ) (hstep : Step e e') : Typing emptyCtx e' τ := by
    -- ...
{% endhighlight lean %}

But it assumes that the type of expressions are already known:
{% highlight lean %}
inductive Expr : Type where
  | num   : Int → Expr 
  | var   : Nat → Expr
  | lam : Ty → Expr → Expr -- The type for the parameter is user-annotated
  -- ...
{% endhighlight lean %}

And there are type checking rules rather than type inferencing rules:
{% highlight lean %}
inductive Typing : Ctx → Expr → Ty → Prop where
  | num (Γ : Ctx) (n : Int) : Typing Γ (Expr.num n) Ty.num
  | if_ (Γ : Ctx) (cnd t e : Expr) (τ : Ty) :
      Typing Γ cnd Ty.bool → Typing Γ t τ → Typing Γ e τ → Typing Γ (Expr.if_ cnd t e) τ
  | var (Γ : Ctx) (i : Nat) (τ : Ty) (h : Γ i = some τ) : Typing Γ (Expr.var i) τ
  | lam (Γ : Ctx) (τ₁ : Ty) (e : Expr) (τ₂ : Ty) :
  -- ...
{% endhighlight lean %}

So it's a fancier version of [CS242 final](https://stanford-cs242.github.io/f19/assignments/final/lean/), not a proof of the type inference algorithm.

What's worse, the agent gets confused about the simplified de Bruijn substitution schema and creating something weird mixture of list and a function that are supposed to be the context:
{% highlight lean %}
abbrev Ctx := Nat → Option Ty

def emptyCtx : Ctx := fun _ => none

def extendCtx (τ : Ty) (Γ : Ctx) : Ctx :=
  fun i =>
    match i with
    | 0 => some τ
    | i+1 => Γ i

-- It's using both the list of type and the context
theorem weaken_prep (Δ : List Ty) (Γ : Ctx) (e : Expr) (τ : Ty) (h : Typing (prepCtx Δ emptyCtx) e τ) : Typing (prepCtx Δ Γ) e τ := by
-- ...
{% endhighlight lean %}

## Second Attempt

I decided to give the agent another chance: cleaning up the mess and run it again. Specifically, I
- Gave up the idea that the agent can prove the correctness of the algorithm and the type safety in one shot.
- Removed anything related to `Ctx`. Just use a list of types as context.
- Added a constraint that the de Bruijn index of variables should always be smaller than the length of the list (described in the `Fin Γ.length` below). This makes it impossible to have free variables in expressions:
{% highlight lean %}
inductive Typing : List Ty → Expr → Ty → Prop where
  -- ...
  | var (Γ : List Ty) (i : Fin Γ.length) (τ : Ty) (h : Γ.get i = some τ) : Typing Γ (Expr.var i) τ
{% endhighlight lean %}
- Told the agent to remove every `sorry` in the file.

During this attempt, I noticed that sometimes the agent provides a proof with some minor mistakes, then it gets frustrated, resets the edit and starts it from scratch, although it's clear that the agent doesn't make any mistake organizing the proof, and it is able to finish it in a fresh new session.

After resetting context for a few times, the agent successfully removed every `sorry` in the file, so I got a correct type safety proof. The entire proof costs about 15￥.

## Looking at the Generated Proof

Let's have a look at the proof to understand how it works.

> Warning: Reading the proof is like reading assembly code: there's a ton of annoying details, and it's not very useful for understanding the full picture. You can just believe that the proof is correct because ~~who cares if everyone is vibe-coding and not looking at the slop they generated~~ we trust the Lean's type checker [^note1] and there are no errors.

[^note1]: Theorems in Lean 4 are types, and a theorem is proven by constructing a value of that type, so we are proving a type checker's correctness using another type checker whose correctness can not be proven in Lean 4.

`Step` encodes the dynamic semantics:
{% highlight lean %}
inductive Step : Expr → Expr → Prop where
  | addL (op : AddOp) (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.addOp op e₁ e₂) (Expr.addOp op e₁' e₂)
  | addR (op : AddOp) (v₁ e₂ e₂' : Expr) (hv : Value v₁) (h : Step e₂ e₂') : Step (Expr.addOp op v₁ e₂) (Expr.addOp op v₁ e₂')
  | addAdd (n₁ n₂ : Int) : Step (Expr.addOp AddOp.add (Expr.num n₁) (Expr.num n₂)) (Expr.num (n₁ + n₂))
  | addSub (n₁ n₂ : Int) : Step (Expr.addOp AddOp.sub (Expr.num n₁) (Expr.num n₂)) (Expr.num (n₁ - n₂))
  | mulL (op : MulOp) (e₁ e₁' e₂ : Expr) (h : Step e₁ e₁') : Step (Expr.mulOp op e₁ e₂) (Expr.mulOp op e₁' e₂)
  | mulR (op : MulOp) (v₁ e₂ e₂' : Expr) (hv : Value v₁) (h : Step e₂ e₂') : Step (Expr.mulOp op v₁ e₂) (Expr.mulOp op v₁ e₂')
  -- ...
{% endhighlight lean %}

`subst` encodes substitution rules:
{% highlight lean %}
def subst (k : Nat) (s : Expr) : Expr → Expr
  | Expr.num n => Expr.num n
  | Expr.addOp o l r => Expr.addOp o (subst k s l) (subst k s r)
  -- ...
  | Expr.var i => if i == k then s else Expr.var i
  | Expr.lam τ e => Expr.lam τ (subst (k+1) s e)
  | Expr.app f a => Expr.app (subst k s f) (subst k s a)
  -- ...
{% endhighlight lean %}

Progress uses structural induction over the expressions. Every case corresponds to a `Step` or a `Val`:
{% highlight lean %}
theorem progress (e : Expr) (τ : Ty) (h : Typing [] e τ) : Value e ∨ ∃ e', Step e e' := by
  induction e generalizing τ with -- `generalizing τ` here make sure that we can use a diffenent `τ` in IH
  | num n => left; exact Value.num
  | addOp op l r ih_l ih_r =>
    match h with
    | Typing.addOp _ _ _ _ hl hr =>
      -- Use the IH (the left has the type `num`) to get that `Value l ∨ ∃ e', Step l e'`
      rcases ih_l Ty.num hl with (hvl | ⟨l', hl'⟩)
      -- If `Value l`, use the IH (the right has the type `num`) to get the result for `r`
      · rcases ih_r Ty.num hr with (hvr | ⟨r', hr'⟩)
        -- If `Value l` and `Value r`, it steps to `l + r`.
        · rcases canonical_num l hvl hl with ⟨nl, rfl⟩; rcases canonical_num r hvr hr with ⟨nr, rfl⟩
          right; cases op with | add => exact ⟨_, Step.addAdd nl nr⟩ | sub => exact ⟨_, Step.addSub nl nr⟩
        · right; exact ⟨_, Step.addR op l r r' hvl hr'⟩ -- If `Step r e'`, we use `addR`.
      · right; exact ⟨_, Step.addL op l l' r hl'⟩ -- If `Step l e'`, we use `addL`.
  -- ...
{% endhighlight lean %}
where `canonical_num` says: if an expression has type `Ty.num`, then it must be a `Expr.num`:
{% highlight lean %}
theorem canonical_num (e : Expr) (hv : Value e) (ht : Typing [] e Ty.num) : ∃ n : Int, e = Expr.num n := by
  cases hv
  -- Using the definition of `Val.num` and get an `Expr.num n`.
  case num => rename_i n; exact ⟨n, rfl⟩
  -- Using the definition of `Val.var` and get an `Fin [].length`, which forms a contradiction.
  case var =>
    cases ht
    · rename_i i h -- 
      exact absurd i.isLt (Nat.not_lt_zero _)
  -- Other values won't have a case that has type `num`, so an empty `cases ht` proves them.
  all_goals { cases ht }
{% endhighlight lean %}

Preservation uses structural induction over `Step`. Most type information is easy to get since it's already annotated. The tricky part is the substitution when applying lambda expressions.
{% highlight lean %}
theorem preservation (e e' : Expr) (τ : Ty) (h : Typing [] e τ) (hstep : Step e e') : Typing [] e' τ := by
  induction hstep generalizing τ with
  | addL op e₁ e₁' e₂ hstep' ih =>
    match h with
    -- `h` is `addOp`, so the old expression has type `num`. Then we need to prove that
    -- the new expression also has type `num`
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp [] op _ _ (ih Ty.num hl) hr
  | addR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp [] op _ _ hl (ih Ty.num hr)
  | addAdd n₁ n₂ =>
    match h with
    | Typing.addOp _ _ _ _ _ _ => exact Typing.num [] (n₁ + n₂)
  -- ...
  | appLam τ₁ body v hv =>
    match h with
    | Typing.app _ _ _ _ τ₂ hf ha =>
      match hf with
      | Typing.lam _ _ _ _ hb => exact subst_typing v body τ₂ τ₁ (@List.nil Ty) hb ha
  -- ...
{% endhighlight lean %}

`subst_typing` says if \(\Gamma,\sigma\vdash e:\tau\) and \(\vdash s:\sigma\), then \(\Gamma\vdash[\left<|\Gamma|\right>\to s]_D\,e:\tau\). Its proof is a structural induction over \(e\).
{% highlight lean %}
theorem subst_typing (s e : Expr) (τ σ : Ty) (Γ : List Ty)
    (h_e : Typing (Γ ++ [σ]) e τ) (h_s : Typing [] s σ) : Typing Γ (subst (Γ.length) s e) τ := by
  induction e generalizing Γ τ with
  -- For most cases, we can use the definition of substitution rules to reduce the problem to trivial results (which is what `simp [subst]` does)
  -- Substitution rule doesn't change the constants.
  | num n => cases h_e; case num => simp [subst]; exact Typing.num Γ n
  -- ...
  -- The substitution on addOp reduces to the substitution on its left and right.
  -- Then we use the IH on both side and know that both side has type `num` so
  -- the entire expression has type `num` by the typing rule.
  | addOp op l r ih_l ih_r => cases h_e; case addOp =>
    simp [subst]; rename_i hl hr; apply Typing.addOp Γ op _ _ (ih_l Ty.num Γ hl) (ih_r Ty.num Γ hr)
  -- ...
  | var i => cases h_e; case var hi hget =>
    by_cases h_eq : hi.val = Γ.length
    -- If `i = Γ.length`, then `var i` is the variable to be substituted.
    · have h_σ_eq : σ = τ := by
      -- Because `var i` has type `τ` and `σ` is the i-th element in the context, we have `σ = τ`.
        have h_val : (Γ ++ [σ]).get hi = σ := get_append_singleton (j := hi) h_eq
        have heq1 : some ((Γ ++ [σ]).get hi) = some σ := congrArg some h_val
        exact Option.some.inj (heq1.symm.trans hget)
      -- We get `Typing Γ (subst Γ.length s (var i)) σ` after substituting `σ = τ`
      -- and `Typing Γ s σ` after using the definition of `subst`. There is a lemma
      -- to fill the gap between `Typing [] s σ` and `Typing Γ s σ`.
      subst h_σ_eq; simp [subst, h_eq]; exact weakening h_s Γ
    -- If `i != Γ.length`, then `subst (Γ.length) s e`'s type is the i-th element of `Γ`,
    · have h_lt : hi.val < Γ.length := by
      -- `i != Γ.length` and we claimed that `i <= Γ.length`, so `i < Γ.length`.
        have h_bound : hi.val < (Γ ++ [σ]).length := hi.isLt
        have h_len : (Γ ++ [σ]).length = Γ.length + 1 := by simp
        have : hi.val < Γ.length + 1 := by simpa [h_len] using h_bound
        omega
      simp [subst, h_eq]
      -- `hget'` says the i-th element of `Γ` is `τ`.
      -- Note: In the original proof, the left hand side is `some (Γ.get ⟨hi.val, h_lt⟩)`.
      -- These two are equivalent since `Γ.get` returns an `Option` and Lean automatically
      -- performs monadic join on `Option`s.
      have hget' : Γ.get ⟨hi.val, h_lt⟩ = some τ := by
        -- The i-th element of `Γ` is the i-th element of `Γ ++ [σ]` (which is proven by
        -- the lemma), so it is `τ` as well.
        have h_val : (Γ ++ [σ]).get hi = Γ.get ⟨hi.val, h_lt⟩ :=
          get_append_left (i := ⟨hi.val, h_lt⟩) (hi := hi.isLt)
        exact heq.symm ▸ hget
      exact Typing.var Γ ⟨hi.val, h_lt⟩ τ hget'
  -- The substitution on lam reduces to the substitution on its body.
  -- We can use the IH on `body` and `τ₁ :: Γ` (which is another way to write `[τ₁] ++ Γ`)
  -- the entire expression has the correct type by the typing rule.
  | lam τ₁ body ih => cases h_e; case lam =>
    simp [subst]; rename_i τ₂ hb; apply Typing.lam Γ τ₁ _ τ₂ (ih τ₂ (τ₁ :: Γ) hb)
  -- ...
{% endhighlight lean %}

The `weakening` lemma says if \(\Gamma'\vdash e:\tau\), then \(\Gamma',\Delta\vdash e:\tau\). It's an induction over the typing rule \(\Gamma'\vdash e:\tau\).
{% highlight lean %}
theorem weakening {Γ' : List Ty} {e : Expr} {τ : Ty} (h : Typing Γ' e τ) (Δ : List Ty) : Typing (Γ' ++ Δ) e τ := by
  induction h generalizing Δ with
  | num Γ n => exact Typing.num (Γ ++ Δ) n -- Constants are always constants.
  -- `addOp` delegates the proof to its LHS and RHS.
  | addOp Γ op l r hl hr ih_l ih_r => exact Typing.addOp (Γ ++ Δ) op l r (ih_l Δ) (ih_r Δ)
  | var Γ i τ hget =>
    -- `i < Γ.length` by typing rules, so `i < (Γ ++ Δ).length`.
    have hi : i.val < (Γ ++ Δ).length := by
      have h_i_lt : i.val < Γ.length := i.isLt
      have h_len : Γ.length ≤ (Γ ++ Δ).length := by simp
      exact Nat.lt_of_lt_of_le h_i_lt h_len
    let i' : Fin (Γ ++ Δ).length := ⟨i.val, hi⟩
    -- The i-th element of `Γ ++ Δ` is the i-th element of `Γ`, so it should also be `τ`.
    -- `get_append_left` is used again.
    have hget' : (Γ ++ Δ).get i' = some τ := (congrArg some get_append_left).trans hget
    exact Typing.var (Γ ++ Δ) i' τ hget'
  -- `lam` prepends a type to the list, so appending `Δ` doesn't affect `lam`.
  | lam Γ τ₁ e τ₂ hb ih => exact Typing.lam (Γ ++ Δ) τ₁ e τ₂ (by simpa using ih Δ)
{% endhighlight lean %}

The `get_append_singleton` lemma says if \(j=|\Gamma|\), then the \(j\)-th element of \(\Gamma,\sigma\) is \(\sigma\). The proof is not as simple as it sounds.
{% highlight lean %}
theorem get_append_singleton {Γ : List Ty} {σ : Ty} {j : Fin ((Γ ++ [σ]).length)} (h_eq : j.val = Γ.length) : (Γ ++ [σ]).get j = σ := by
  induction Γ with
  | nil => simp -- Base case: the result is trivial if Γ is empty.
  | cons τ Γ' ih => -- Inductive case `Γ = τ :: Γ'`.
    cases j; rename_i val isLt
    cases val with
    -- If `j = 0`, then `Γ.length = 0`, which forms contradiction.
    | zero => have : 0 = (τ :: Γ').length := h_eq; simp at this
    -- `j = n + 1`, so the `j`-th element of `Γ ++ [σ]` is the `n`-th element of `Γ' ++ [σ]`
    -- and we can use IH to prove that the `n`-th element of `Γ' ++ [σ]` is `σ`.
    -- There are many inferences hidden in `simpa`.
    | succ n =>
      have h_lt : n < (Γ' ++ [σ]).length := by
        have : n.succ < ((τ :: Γ') ++ [σ]).length := isLt; simpa using this
      have h_eq' : n = Γ'.length := by simp at h_eq; exact h_eq
      simpa using ih (j := ⟨n, h_lt⟩) h_eq'
{% endhighlight lean %}

Finally, the `get_append_left` lemma that says the i-th element of `Γ ++ Δ` is equal to the i-th element of `Γ`.
{% highlight lean %}
theorem get_append_left {Γ Δ : List Ty} {i : Fin Γ.length} {hi : i.val < (Γ ++ Δ).length} : (Γ ++ Δ).get ⟨i.val, hi⟩ = Γ.get i := by
  induction Γ with
  -- Base case: if Γ is empty, then it's impossible to get the i-th element.
  | nil => exact Fin.elim0 i
  | cons τ Γ' ih => -- Inductive case `Γ = τ :: Γ'`.
    cases i; rename_i val isLt
    cases val with
    | zero => rfl -- If `i = 0`, then it becomes `τ = τ`.
    -- `i = n + 1`, so the `i`-th element of `Γ` or `Γ ++ Δ` is the `n`-th element
    -- of `Γ'` or `Γ' ++ Δ`. We can use IH to prove that the last two are equal so
    -- the first two are also equal.
    | succ n =>
      have h_n_lt : n < Γ'.length := by simp at isLt; exact isLt
      have hi_n : n < (Γ' ++ Δ).length := by
        have : n.succ < ((τ :: Γ') ++ Δ).length := hi; simpa using this
      simpa using ih (i := ⟨n, h_n_lt⟩) (hi := hi_n)
{% endhighlight lean %}

## Conclusion

- The barrier of writing formal proofs has been significantly lowered, thanks to AI agents.
- Agents are extremely capable of removing `sorry`s in the proof (if it is provable), but they will go astray if you let them design structures and theorems.
- These parts never gets easier since no AI agent can do that for you:
  - Knowing what to prove and what can prove.
  - Defining things correctly to represent what you want to prove.
  - Understanding the proof.
