---
layout: post
title:  "Type Safety Proof (Part 1)"
---

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

What's worse, the simplified de Bruijn substitution schema is completely ignored. It's annoying that the agent uses the canonical substitution rule without my approval. Maybe there is a bug in the rules and the agent don't know how to prove it, but at lease it should say "I'm not able to prove your simplified schema" rather than presenting something that looks similar but completely different and say "This is what you want".

## Conclusion

Formal verification is hard, even with the help of AI. AI agents are good enough at proving theorems, but the things they prove may not be the things you want. To make sure that AI proves the correct thing, we have to design the structure and theorems manually. That part never gets easier.

As for this project, I'll try to finish the substitution part by hand, and see if I can use the result to further prove the type inference algorithm.

## Appendix: Looking at the Generated Proof

Let's have a look at the proof to understand how it works.

The `Step` encodes the dynamic semantics:
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

Progress uses structural induction over the expression:
{% highlight lean %}
theorem progress (e : Expr) (τ : Ty) (h : Typing emptyCtx e τ) : Value e ∨ ∃ e', Step e e' := by
  induction e generalizing τ with
  | num n => left; exact Value.num
  | addOp op l r ih_l ih_r =>
    match h with
    | Typing.addOp _ _ _ _ hl hr =>
      rcases ih_l Ty.num hl with (hvl | ⟨l', hl'⟩) -- Use the IH to get that `Value l ∨ ∃ e', Step l e'`
      · rcases ih_r Ty.num hr with (hvr | ⟨r', hr'⟩) -- If `Value l`, use the IH to get the result for `r`
        -- If `Value l` and `Value r`, it steps to `l + r`.
        · rcases canonical_num l hvl hl with ⟨nl, rfl⟩; rcases canonical_num r hvr hr with ⟨nr, rfl⟩
          right; cases op with | add => exact ⟨_, Step.addAdd nl nr⟩ | sub => exact ⟨_, Step.addSub nl nr⟩
        · right; exact ⟨_, Step.addR op l r r' hvl hr'⟩ -- If `Step r e'`, we use `addR`.
      · right; exact ⟨_, Step.addL op l l' r hl'⟩ -- If `Step l e'`, we use `addL`.
  -- ...
{% endhighlight lean %}

Preservation uses structural induction over `Step`. Most type information is easy to get since it's already annotated:
{% highlight lean %}
theorem preservation (e e' : Expr) (τ : Ty) (h : Typing emptyCtx e τ) (hstep : Step e e') : Typing emptyCtx e' τ := by
  induction hstep generalizing τ with
  | addL op e₁ e₁' e₂ hstep' ih =>
    match h with
    -- `h` is `addOp`, so the old expression has type `num`. Then we need to prove that
    -- the new expression also has type `num`
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp emptyCtx op _ _ (ih Ty.num hl) hr
  | addR op v₁ e₂ e₂' hv hstep' ih =>
    match h with
    | Typing.addOp _ _ _ _ hl hr => exact Typing.addOp emptyCtx op _ _ hl (ih Ty.num hr)
  | addAdd n₁ n₂ =>
    match h with
    | Typing.addOp _ _ _ _ _ _ => exact Typing.num emptyCtx (n₁ + n₂)
  -- ...
{% endhighlight lean %}

The tricky part is the substitution when applying lambda expression.
{% highlight lean %}
-- In Step
  | appLam (τ : Ty) (body v : Expr) (hv : Value v) : Step (Expr.app (Expr.lam τ body) v) (subst 0 v body)

-- In progress
  | lam σ body ih_body => left; exact Value.lam
  | app f a ih_f ih_a =>
    match h with
    | Typing.app _ _ _ τ₁ τ₂ hf ha =>
      rcases ih_f (Ty.fn τ₁ τ₂) hf with (hvf | ⟨f', hf'⟩)
      · match hf with
        | Typing.lam _ _ body _ hb =>
          rcases ih_a τ₁ ha with (hva | ⟨a', ha'⟩)
          · right; exact ⟨_, Step.appLam τ₁ body a hva⟩
          · right; exact ⟨_, Step.appR (Expr.lam τ₁ body) a a' Value.lam ha'⟩
      · right; exact ⟨_, Step.appL f f' a hf'⟩

-- In preservation
  | appLam τ₁ body v hv =>
    match h with
    | Typing.app _ _ _ _ τ₂ hf ha =>
      match hf with
      | Typing.lam _ _ _ _ hb => exact subst_typing body v τ₁ τ₂ hb ha
{% endhighlight lean %}

`subst_typing` says if \(\tau\vdash e_{\mathsf{body}}:\tau_{\mathsf{out}}\) and \(\vdash s:\tau\), then \(\vdash[\left<0\right>\to s]_D\,e_{\mathsf{body}}:\tau_{\mathsf{out}}\).
{% highlight lean %}
theorem subst_typing (body s : Expr) (τ τ_out : Ty)
    (h_body : Typing (extendCtx τ emptyCtx) body τ_out) (h_s : Typing emptyCtx s τ) : Typing emptyCtx (subst 0 s body) τ_out := by
    -- ...
{% endhighlight lean %}

Its proof contains hundreds of lines of incomprehensible theorems, and I'm not going to waste my (and your) time to read it.
