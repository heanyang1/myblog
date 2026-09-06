---
layout: post
title:  "Soundness of Sign Analysis (Part 3)"
---

> This is the last post of a series about me learning static analysis. Here's [the previous post](/myblog/2026/08/09/dfa-with-category-theory.html).

In the first post of this series, we derived our sign analysis function \(P\to(V\to \mathcal{S})\). Now we can finally define and prove the soundness of the function.

## Collecting Semantics

Let's begin with a question: is there a "ground truth" value given a sign analysis problem? Consider the StaPL program
```
x = 1
y = -3
input z
loop: if z goto end
x = x + 2
y = -y
input z
if 1 goto loop
end: put x
```

Intuitively, we know that the sign of `x` should be \(+\), `y` and `z` be \(\top\) when the program ends (let's denote it as the program point \(p\)). We can prove our conjecture by running the program on every input and collect every possible value of the variables at \(p\). Let \(\mathrm{collect}(p)\in V\to\mathcal{P}(\mathbb{Z})\) be the set of the possible values of \(x\) at program point \(p\), we have:
\[\mathrm{collect}(p)(x)=\{2w+1|w\in\mathbb{Z}_+\},\quad\mathrm{collect}(p)(y)=\{3,-3\},\quad\mathrm{collect}(p)(z)=\mathbb{Z}.\]

And the "ground truth" sign of the variable \(x\) is given by passing \(\mathrm{collect}(p)(x)\) to the *abstraction function*
\[\alpha(D)=\begin{cases}
\perp, & D=\varnothing, \\
+, & D\neq\varnothing\wedge D\subseteq\mathbb{Z}_+, \\
-, & D\neq\varnothing\wedge D\subseteq\mathbb{Z}_-, \\
0, & D=\{0\}, \\
\top, & \text{otherwise}. \\
\end{cases}\]

To verify that \(\alpha:\mathcal{P}(\mathbb{Z})\to\mathcal{S}\) is a monotone map, we need to prove that for every \(D_1,D_2\in\mathcal{P}(\mathbb{Z})\), if \(D_1\subseteq D_2\), then \(\alpha(D_1)\sqsubseteq\alpha(D_2)\). This can be done by assuming that \(D_1\subseteq D_2\) but \(\alpha(D_1)\not\sqsubseteq\alpha(D_2)\), then enumerating every cases of \(\alpha(D_1)\) and \(\alpha(D_2)\) to show that it's impossible.

Conversely, there is a *concretization function* \(\gamma:\mathcal{S}\to\mathcal{P}(\mathbb{Z})\) that assigns a sign to the biggest set it can represent:
\[\gamma(s)=\begin{cases}
\varnothing, & s=\perp, \\
\mathbb{Z}_+, & s=+, \\
\mathbb{Z}_-, & s=-, \\
\{0\}, & s=0, \\
\mathbb{Z}, & s=\top. \\
\end{cases}\]

It's easy to verify that \(\gamma\) is a monotone map, and for every \(D\in\mathcal{P}(\mathbb{Z}),s\in\mathcal{S}\), \(\alpha(D)\sqsubseteq s\) iff \(D\subseteq\gamma(s)\), so \(\alpha\dashv\gamma\).

Functions like \(\mathrm{collect}(p)\) are called a *collecting semantics* of StaPL. The way we derive \(\mathrm{collect}\) is (un)surprisingly similar to data flow analysis:
1. For a statement \(s\in S\), there is a transfer function \(\mathrm{transfer}(s)\) that inputs \(\mathrm{collect}(\mathrm{begin}(s))(x)\) and outputs \(\mathrm{collect}(\mathrm{end}(s))(x)\). The definition of the \(\mathrm{transfer}(s)\) will be given later.
2. Let \(\mathrm{pred}(s)\) be the set of predecessor of statement \(s\), then \[\mathrm{collect}(\mathrm{begin}(s))(x)=\bigcup_{t\in\mathrm{pred}(s)}\mathrm{collect}(\mathrm{end}(t))(x).\]
3. We end up solving a set of equations \[x_i=\mathrm{transfer}(s_i)\left(\bigcup_{j\in\{k|s_k\in\mathrm{pred}(s_i)\}}x_j\right),\ i=1,2,\dots,|S|,\tag{1}\]

The solution to equation (1) is a fixed point of a function \(G:\mathcal{P}(\mathbb{Z})^{|S|}\to\mathcal{P}(\mathbb{Z})^{|S|}\). We can prove that it's a monotone function like what we've done in part 1, but we are not able to solve the equations with the fixed point theorem because \(\mathcal{P}(\mathbb{Z})\) is an infinite lattice. Nevertheless, the least fixed point exists and is unique due to the Tarski's fixed point theorem:

**Theorem 1.** Let \(L\) be a complete lattice. Every monotone function \(f:L\to L\) has a unique least fixed point, denoted as \(\mathrm{lfp}(f)\).

*proof.* We claim that \(\mathrm{lfp}(f)=\sqcap D\), where \(D=\{x\in L|x\sqsupseteq f(x)\}\).

By definition of \(\sqcap D\), for every \(x\in D\), \(x\sqsupseteq \sqcap D\). Because \(f\) is monotone map, therefore \(f(x)\sqsupseteq f(\sqcap D)\). Because \(x\in D\), therefore \(x\sqsupseteq f(x)\), therefore for every \(x\in D\), \(x\sqsupseteq f(\sqcap D)\), which means \(f(\sqcap D)\) is a lower bound of \(D\). By definition, \(\sqcap D\sqsupseteq f(\sqcap D)\), therefore \(\sqcap D\in D\).

Because \(f\) is monotone map, therefore for every \(x\in D\), if \(x\sqsupseteq f(x)\) then \(f(x)\sqsupseteq f(f(x))\), therefore \(f(x)\in D\). By definition of \(\sqcap D\), \(f(x)\sqsupseteq\sqcap D\). Because \(\sqcap D\in D\), therefore \(f(\sqcap D)\sqsupseteq\sqcap D\). By anti-symmetry, \(f(\sqcap D)=\sqcap D\), so \(\sqcap D\) is a fixed point.

For every fixed point \(x\) of \(f\), \(x\sqsupseteq f(x)\), therefore \(x\in D\) and \(x\sqsupseteq\sqcap D\), therefore \(\sqcap D\) is the least fixed point. The uniqueness can be proved by the uniqueness of the products introduced in part 2. \(\Box\)

## Soundness

Let's generalize the problem a bit using category theory. Say we need to estimate a functor \(G:\mathcal{D}_1\to \mathcal{D}_2\) using another functor \(F:\mathcal{C}_1\to \mathcal{C}_2\). We say that \(F\) is *sound* if it's always pessimistic compared to \(G\). To be specific, let \(L_1\dashv R_1,L_2\dashv R_2\) be the adjunction pairs between \(\mathcal{C}_1,\mathcal{D}_1\) and \(\mathcal{C}_2,\mathcal{D}_2\) respectively, then for every \(d\in \mathrm{Ob}(\mathcal{D}_1)\), \(\mathcal{C}_2(L_2Gd,FL_1d)\) is not empty (there is always a morphism \(L_2Gd\to FL_1d\) in \(\mathcal{C}_2\)).

The following lemma provides an alternative definition to soundness:

**Lemma 1.** \(F\) is sound iff for every \(c\in \mathrm{Ob}(\mathcal{C}_1)\),\(\mathcal{D}_2(GR_1c,R_2Fc)\) is not empty.

*proof.* Both directions are similar. We only prove the (\(\Rightarrow\)) here.

Assume (on the contrary) that there exists \(c\in\mathrm{Ob}(\mathcal{C}_1)\) such that \(\mathcal{D}_2(GR_1c,R_2Fc)\) is empty. Because \(L_2\dashv R_2\), therefore \(\mathcal{C}_2(L_2(GR_1c),Fc)\cong\mathcal{D}_2(GR_1c,R_2(Fc))\), so \(\mathcal{C}_2(L_2GR_1c,Fc)\) is empty.

Because \(F\) is sound, therefore \(\mathcal{C}_2(L_2G(R_1c),FL_1(R_1c))\) is not empty. Therefore there exists a morphism \(f:L_2GR_1c\to FL_1R_1c\).

Let \(\varepsilon\) be the counit of \(L_1\vdash R_1\), then \(F\varepsilon_c\) is a morphism \(FL_1R_1c\to Fc\). So we have a morphism \(F\varepsilon_c\circ f:L_2GR_1c\to Fc\), which contradicts that \(\mathcal{C}_2(L_2GR_1c,Fc)\) is empty. \(\Box\)

In our sign analysis example, \(\mathcal{D}_1=\mathcal{D}_2=\mathcal{P}(\mathbb{Z})^{|S|}\), \(\mathcal{C}_1=\mathcal{C}_2=\mathcal{S}^{|S|}\), \(L_1=L_2=\alpha'\) is the vectorized version of \(\alpha\) that maps \((D_1,\dots,D_{|S|})\) to \(\alpha(D_1),\dots,\alpha(D_{|S|})\), \(R_1=R_2=\gamma'\) is the vectorized \(\gamma\), \(F:\mathcal{S}^{|S|}\to\mathcal{S}^{|S|}\) is the functor derived from the equations that generates sign analysis results in Part 1, and \(G:\mathcal{P}(\mathbb{Z})^{|S|}\to\mathcal{P}(\mathbb{Z})^{|S|}\) is derived from the equations (1) in this post. To verify the soundness of sign analysis, we need to prove that
1. \(F\) is a sound estimate of \(G\).
2. If \(F\) is a sound, then the analysis result is sound. This is called *the soundness theorem* in SPA book.

The first part can be done mechanically by decomposing \(F\) and \(G\) into small pieces and prove that the morphism always exists, like what we have done in Part 1 [^proof]. Let's focus on the soundness theorem.

[^proof]: An AI agent finished the proof in Lean [here](https://github.com/heanyang1/proofs/blob/main/Proofs/Soundness_2026_09_06.lean), but I haven't proofread it yet. It also found some issues within the proofs in this post, and all of them are fixed by hand.

**Theorem 2.** If for every \(d\in\mathcal{S}\), \(G\gamma'd\sqsubseteq \gamma'Fd\), then \(\alpha'(\mathrm{lfp}(G))\sqsubseteq\mathrm{lfp}(F)\).

*proof.* Assigning \(d=\mathrm{lfp}(F)\) in the soundness morphism yields \(G\gamma'\mathrm{lfp}(F)\sqsubseteq \gamma'F\mathrm{lfp}(F)\).

Because \(\mathrm{lfp}(F)\) is a fixed point of \(F\), therefore \(\gamma'F\mathrm{lfp}(F)=\gamma'\mathrm{lfp}(F)\). Therefore \(G\gamma'\mathrm{lfp}(F)\sqsubseteq \gamma'\mathrm{lfp}(F)\). Therefore \(\gamma'\mathrm{lfp}(F)\in\{x|x\sqsupseteq Gx\}\).

From the proof of theorem 1, we know that \(\mathrm{lfp}(G)=\sqcap\{x|x\sqsupseteq Gx\}\), therefore \(\mathrm{lfp}(G)\sqsubseteq\gamma'\mathrm{lfp}(F)\).

By the proposition 4 in Part 2, \(\alpha'\dashv\gamma'\), so \(\alpha'(\mathrm{lfp}(G))\sqsubseteq\mathrm{lfp}(F)\). \(\Box\)

## Outro

I haven't finished the entire SPA book yet, and many topics are not covered, but I decided to end this series because the learning process is longer than expected, and what I have learned is already enough for my work.

Some closing thoughts after learning it in the past few months:
- It's easy to "feels" that an analysis is correct, but it's hard to prove it.
- Although I'm a bit familiar with adjunction now, I'm still not very good at juggling two categories at once and often mess things up.
- I prefer the notations in category theory than those in the book.

I'm planning to learn [MIT 18.404J - Theory of Computation](https://ocw.mit.edu/courses/18-404j-theory-of-computation-fall-2020/) for hobby and [KAIST CS420 - Compiler Design](https://github.com/kaist-cp/cs420.git) for job in later months. Hopefully I'll find something interesting and post it here.
