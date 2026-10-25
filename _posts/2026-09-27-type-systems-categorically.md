---
layout: post
title:  "Understanding Type Systems with Category Theory"
---

> Update on 10/25: I decided to publish this update despite that it's incomplete, because the previous version is a complete disaster.

In the beginning of [the assignments 6 of Stanford CS242](https://stanford-cs242.github.io/f19/assignments/assign6/), there is a quote from [linear logic's Wikipedia page](https://en.wikipedia.org/wiki/Linear_logic):
> "In terms of simple denotational models, linear logic may be seen as refining the interpretation of intuitionistic logic by replacing cartesian (closed) categories by symmetric monoidal (closed) categories ..."

This feels like an abstract nonsense to me when learning CS242, but after learning some basics of category theory, I realized that this does capture the essence of linear types. In fact, I think symmetric monoidal closed categories is *the only correct way* to understand linear type systems like the one in Rust [^lambda_quote].

[^lambda_quote]: There is [a similar claim](https://math.ucr.edu/home/baez/act_course/lecture_2.html) by John Baez that he can only understand lambda calculus via (probably cartesian closed) categories.

In the next several posts, I'll try to decipher the sentence so it can be digested by us mortals. I'll assume that you are familiar with the concepts in [my previous post about category theory](/myblog/2026/08/09/dfa-with-category-theory.html).

## The Language

A subset of the typed lambda calculus in CS242 will be used throughout the post [^ocr]:
\[\begin{aligned}
\mathsf{Type}~\tau \ ::={} & \mathsf{unit} \\
& \mid\;\ \mathsf{void} \\
& \mid\;\ \tau_{arg} \to \tau_{ret} \\
& \mid\;\ \tau_L \times \tau_R \\
& \mid\;\ \tau_L + \tau_R \\[2ex]
\mathsf{Expression}~e \ ::={} & x \\
& \mid\;\ \lambda\ (x:\tau)\,.\ e \\
& \mid\;\ e_{lam}\ e_{arg} \\
& \mid\;\ () \\
& \mid\;\ (e_L,\ e_R) \\
& \mid\;\ e\,.\,d \\
& \mid\;\ \mathsf{inj}\ e = d\ \mathsf{as}\ \tau \\
& \mid\;\ \mathsf{case}\ e\ \{L(x_L) \to e_L\ \mid\ R(x_R) \to e_R\} \\[2ex]
\mathsf{Direction}~d \ ::={} & L\;\mid\;R
\end{aligned}\]
\[\dfrac{\Gamma,\ x : \tau_{arg} \vdash e : \tau_{ret}}
      {\Gamma \vdash (\lambda\ (x : \tau_{arg})\,.\ e) : \tau_{arg} \to \tau_{ret}}~~\text{(T-Lam)}\]
\[\dfrac{\Gamma \vdash e_{lam} : \tau_{arg} \to \tau_{ret} \qquad \Gamma \vdash e_{arg} : \tau_{arg}}
      {\Gamma \vdash (e_{lam}\ e_{arg}) : \tau_{ret}}~~\text{(T-App)}\]
\[\dfrac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}~~\text{(T-Var)}\quad\dfrac{}{\Gamma\vdash () : \mathsf{unit}}~~\text{(T-Unit)}\]
\[\dfrac{\Gamma \vdash e_L : \tau_L \qquad \Gamma \vdash e_R : \tau_R}
      {\Gamma \vdash (e_L,\ e_R) : \tau_L \times \tau_R}~~\text{(T-Pair)}\]
\[\dfrac{\Gamma \vdash e : \tau_L \times \tau_R}{\Gamma \vdash e.L : \tau_L}~~\text{(T-Project-L)}
\qquad
\dfrac{\Gamma \vdash e : \tau_L \times \tau_R}{\Gamma \vdash e.R : \tau_R}~~\text{(T-Project-R)}
\]
\[
\frac{\Gamma \vdash e : \tau_L}
     {\Gamma \vdash \mathsf{inj}\ e = L\ \mathsf{as}\ \tau_L + \tau_R : \tau_L + \tau_R}
\ \text{(T-Inject-L)}
\]
\[
\frac{\Gamma \vdash e : \tau_R}
     {\Gamma \vdash \mathsf{inj}\ e = R\ \mathsf{as}\ \tau_L + \tau_R : \tau_L + \tau_R}
\ \text{(T-Inject-R)}
\]
\[
\frac{\Gamma \vdash e : \tau_L + \tau_R
      \quad \Gamma, x_L : \tau_L \vdash e_L : \tau
      \quad \Gamma, x_R : \tau_R \vdash e_R : \tau}
     {\Gamma \vdash \mathsf{case}\ e\ \{L(x_L) \to e_L \mid R(x_R) \to e_R\} : \tau}
\ \text{(T-Case)}
\]

[^ocr]: (a) The grammar is OCRed from a screenshot taken from CS242's assignment 4, (b) some trivial typing rules are omitted.

We are interested in the following properties of the language:
1. There is a \(\mathsf{unit}\) type with exactly one element `()`, and for every type \(\tau\) you can construct a function \(\tau\to\mathsf{unit}\) by returning `()`.
2. For every types \(\tau_1,\tau_2\), we can construct a pair with type \((\tau_1,\tau_2)\) and function with type \(\tau_1\to\tau_2\).
3. Currying \(\tau_1\to(\tau_2\to\tau_3)\Leftrightarrow(\tau_1\times\tau_2)\to\tau_3\) allow us to transform function types to product types and vice versa.
4. There is a \(\mathsf{void}\) that contains has no occupants. For every type \(\tau\), both \(\mathsf{void}+\tau\) and \(\mathsf{void}+\tau\) are isomorphic to \(\tau\).
5. for every types \(\tau_1,\tau_2,\tau_3\), \((\tau_1+\tau_2)+\tau_3\) is isomorphic to \(\tau_1+(\tau_2+\tau_3)\).

As we will see in later sections, the first 3 properties makes the type system a *cartesian closed category* and the last two adds monoidal structure (i.e. makes it a *monoidal category* when viewing from a different angle) to it.

## Cartesian Closed Category

**Definition.**\label{def:ccc} A *cartesian closed category* (CCC) is a category \(\mathcal{C}\) that:
1. has a terminal object,
2. is closed under product, i.e. for every objects \(X,Y\) in \(\mathcal{C}\), \(X\times Y\) exists and is an object of \(\mathcal{C}\), and
3. for every object \(Y\) in \(\mathcal{C}\), the functor \(-\times Y:\mathcal{C}\to\mathcal{C}\) (that maps object \(X\) to \(X\times Y\) and morphism \(f\) to \(f\times\mathrm{id}_Y\)) has a right adjoint.

Here are two examples of CCC:

**Example.**\label{ex:set-ccc} \(\mathsf{Set}\) is cartesian closed.

*proof.* In \(\mathsf{Set}\), any singleton set (the set with one element) can be its terminal object. Let \(S=\{s\}\) be the singleton set we have chosen, then
1. for every set \(X\), there is a function \(X\to S\) that maps everything in \(X\) to \(s\).
2. Suppose (on the contrary) that there are two functions \(f,g:X\to S\) and \(f\neq g\), then there exists \(x\in S\) such that \(f(x)\neq g(x)\), which means \(S\) has at least two different elements (contradiction).

In \(\mathsf{Set}\), the product is cartesian product. It's trivial that \(\mathsf{Set}\) is closed under product.

The right adjoint of \(-\times Y\) can be defined by the *exponential functor* \(-^Y\) that maps \(X\) to \(X^Y=\{f|f:Y\to X\}\) and \(f:X\to Z\) to a function \(f^Y:X^Y\to Z^Y\) such that
\[f^Y(g)=f\circ g\in Z^Y,\quad\forall g\in X^Y.\]

For simplicity, we use \(L\) and \(R\) to denote \(-\times Y\) and \(-^Y\) respectively.

We'll use \ref{lem:adjunction-unit-counit} in previous post to prove that \(L\dashv R\), which means we need to provide two natural transformation \(\varepsilon,\eta\) whose components
\[\varepsilon_X:X^Y\times Y\to X,\quad\eta_Z:Z\to(Z\times Y)^Y\]
have the following properties:
1. For every set \(Z\), if there is a function \(f:Z\times Y\to X\), then there is a unique function \(g:Z\to X^Y\) such that \(f=\varepsilon_X\circ Lg=\varepsilon_X\circ(g\times\mathrm{id}_Y)\).
2. For every set \(X\), if there is a function \(g:Z\to X^Y\), then there is a unique function \(f:Z\times Y\to X\) such that \(g=Rf\circ\eta_Z=f^Y\circ\eta_Z\).

We claim that these two functions are what we want:
1. \(\varepsilon_X\) takes in a function \(h:Y\to X\in X^Y\) and an element \(y\in Y\), and apply \(h\) to \(y\) to get a element in \(X\).
2. \(\eta_Z\) takes in an element \(z\in Z\) and create a function that inputs \(y\in Y\) and outputs \((z,y)\).

We only prove \(\varepsilon\) here, and \(\eta\) is similar.

(Existence) The curried version of \(f\) has the signature \(Z\to X^Y\) and \(f=\varepsilon_X\circ(g\times\mathrm{id}_Y)\).

(Uniqueness) Assume (on the countrary) that there are more than two functions \(g_1,g_2:Z\to X^Y\) such that \(g_1\neq g_2\) and \(f=\varepsilon_X\circ(g_1\times\mathrm{id}_Y)=\varepsilon_X\circ(g_2\times\mathrm{id}_Y)\). Because \(g_1\neq g_2\), therefore there exists \(z\in Z\) such that \(g_1(z)\neq g_2(z)\), therefore there exists \(y\in Y\) such that
\[(g_1(z))(y)\neq(g_2(z))(y)\Rightarrow (\varepsilon_X\circ(g_1\times\mathrm{id}_Y))(z,y)\neq(\varepsilon_X\circ(g_2\times\mathrm{id}_Y))(z,y),\]

Which contradicts \(\varepsilon_X\circ(g_1\times\mathrm{id}_Y)=\varepsilon_X\circ(g_2\times\mathrm{id}_Y)\).

(Naturality) For every function \(f:X_1\to X_2\), consider a pair \((g,y)\in X_1^Y\times Y\). Because
\[f\circ\varepsilon_{X_1}((g,y))=f(\varepsilon_{X_1}((g,y)))=f(g(y)),\]
\[\varepsilon_{X_2}\circ(f^Y\times\mathrm{id}_Y)((g,y))=\varepsilon_{X_2}((f\circ g,y))=f(g(y)),\]
therefore the naturality square for \(\varepsilon\)
\[
\begin{CD}
X_1^Y\times Y @>(f^Y\times\mathrm{id}_Y)>> X_2^Y\times Y \\
@V\varepsilon_{X_1}VV @VV{\varepsilon_{X_2}}V \\
X_1 @>>f> X_2
\end{CD}
\]
commutes. \(\Box\)

**Example.**\label{ex:type-ccc} Let's formalize our previous intuition that the type systems of our language is a CCC.
1. The objects are types.
2. A morphism between two objects \(\tau_1,\tau_2\) is a function with type \(\tau_1\to\tau_2\).
3. There is a \(\mathsf{unit}\) type that for every type \(\tau\), there is exactly one function \(\lambda(x:\tau)\ .\ ()\) with type \(\tau\to\mathsf{unit}\).
4. The product is given by the product type \(\times\) and types are \(\times\)-closed.
5. For every type \(\tau\), the right adjoint to \(-\times\tau\) is \(-^\tau\), where \(\tau_1^{\tau_2}\) is the type of function \(\tau_2\to\tau_1\).

1, 2 and 4 holds by definition of the language. The proof of 3 and 5 are the same as \ref{ex:set-ccc}. See the appendix if you are not convinced by my hand-waving.

As we have seen in \ref{ex:set-ccc}, the counit of the adjunction is related to evaluating functions.

## Monoidal Category

**Definition.**\label{def:monoidal-category} A *monoidal (closed) category* contains following items:
1. a category \(\mathcal{V}\),
2. a bifunctor \(\otimes:\mathcal{V}\times\mathcal{V}\to\mathcal{V}\),
3. an object \(\mathbf{1}\) in \(\mathcal{V}\) such that \(\mathbf{1}\otimes*:\mathcal{V}\to\mathcal{V}\) (denoted as \(\lambda\)) and \(*\otimes\mathbf{1}:\mathcal{V}\to\mathcal{V}\) (denoted as \(\rho\)) are isomorphisms,
4. a natural isomorphism \(\alpha\) on the category of functors \(\mathcal{V}\times\mathcal{V}\times\mathcal{V}\to\mathcal{V}\) that maps \((*\otimes*)\otimes *\) to \(*\otimes(*\otimes*)\), such that the following diagram commutes:
```tikz
\documentclass[tikz]{standalone}
\usepackage{amsmath,amssymb}
\begin{document}
\begin{tikzpicture}
% nodes
\node (top)  at (0, 4.5)    {$((X \otimes Y) \otimes Z) \otimes W$};
\node (lmid) at (-4.1, 2.2) {$(X \otimes (Y \otimes Z)) \otimes W$};
\node (rmid) at (4.1, 2.2)  {$(X \otimes Y) \otimes (Z \otimes W)$};
\node (lbot) at (-3.1, -1.1)   {$X \otimes ((Y \otimes Z) \otimes W)$};
\node (rbot) at (3.1, -1.1)    {$X \otimes (Y \otimes (Z \otimes W))$};
% arrows
\draw[->] (top)  -- node[above left]  {$a(X,Y,Z)\otimes\mathrm{id}_W$} (lmid);
\draw[->] (top)  -- node[above right] {$a(X\otimes Y,Z,W)$} (rmid);
\draw[->] (lmid) -- node[left]        {$a(X,Y\otimes Z,W)$} (lbot);
\draw[->] (rmid) -- node[right]       {$a(X,Y,Z\otimes W)$} (rbot);
\draw[->] (lbot) -- node[below]       {$\mathrm{id}_X\otimes a(Y,Z,W)$} (rbot);
\end{tikzpicture}
\end{document}
```

**Example.**\label{ex:ccc-monoidal} If a category \(\mathcal{C}\) is a CCC, then it is also a monoidal category. Its \(\otimes\) is the product \(\times\), its \(\mathbf{1}\) is the terminal object.

By definition of product:
1. For every object \(X\) in \(\mathcal{C}\), there is a morphism \(f_{X}:\mathbf{1}\times X\to X\).
2. For every object \(Y\) in \(\mathcal{C}\), there is always a morphism \(Y\to\mathbf{1}\), so if there is a morphism \(g:Y\to X\), then there is a unique morphism \(f:Y\to\mathbf{1}\times X\) such that \(g=f_{X}\circ f\).
   - Let \(Y=X\) and \(g=\mathrm{id}_X\), then we have a unique morphism \(h_X\) such that \(\mathrm{id}_{X}=f_{X}\circ h_X\).
   - Let \(Y=\mathbf{1}\times X\) and \(g=h_X\), then we have a unique morphism \(h_{\mathbf{1}}:\mathbf{1}\times X\to\mathbf{1}\times X\) such that \(f_X=f_X\circ h_{\mathbf{1}}\).

     Because \(f_X=f_X\circ\mathrm{id}_{\mathbf{1}\times X}\), therefore \(h_{\mathbf{1}}=\mathrm{id}_{\mathbf{1}\times X}\).

     Because \(f_X\circ(f\circ f_X)=(f_X\circ f)\circ f_X=\mathrm{id}_{X}\circ f_X=f_X\), therefore \(f\circ f_X=h_{\mathbf{1}}=\mathrm{id}_{\mathbf{1}\times X}\).

Therefore \(\mathbf{1}\times *\) is isomorphism. Similarly \(*\times\mathbf{1}\) is isomorphism and \(\mathbf{1}\times\mathbf{1}\cong\mathbf{1}\).

For every object \(X,Y,Z\) in \(\mathcal{C}\), consider the object \((X\times Y)\times Z\):
1. There is a morphism from \((X\times Y)\times Z\) to \(X,Y,Z\) respectively.
2. If there is an object \(W\) with morphism \(W\to X,W\to Y,W\to Z\), then by definition of product, there's also a morphism \(W\to(X\times Y)\), therefore there's a unique morphism \(W\to((X\times Y)\times Z)\).

Therefore \((X\times Y)\times Z=\prod\{X,Y,Z\}\). Similarly, \(X\times(Y\times Z)=\prod\{X,Y,Z\}\). Because products are unique upto isomorphism, therefore \((X\times Y)\times Z\cong X\times(Y\times Z)\). This gives us \(\alpha\). It should be trivial (if not tedious) that for every morphism \(f:(X_1,Y_1,Z_1)\to(X_2,Y_2,Z_2)\) in \(\mathcal{C}\times\mathcal{C}\times\mathcal{C}\), the following square commutes:
\[
\begin{CD}
(X_1\times Y_1)\times Z_1 @>\alpha_{X_1,Y_1,Z_1}>> X_1\times (Y_1\times Z_1) \\
@V((*\times *)\times *)fVV @VV(*\times (*\times *))fV \\
(X_2\times Y_2)\times Z_2 @>\alpha_{X_2,Y_2,Z_2}>> X_2\times (Y_2\times Z_2) \\
\end{CD}
\]

The pentagonal diagram commutes because the isomorphism between products are unique, so there is only one morphism from \(((X \times Y) \times Z) \times W\) to \(X \times (Y \times (Z \times W))\). \(\Box\)

**Example.**\label{ex:linear-monoidal} Our type system (denoted as \(\mathcal{T}\)) has an additional monoidal structure other than the once derived from CCC:
- Its \(\otimes\) is \(+\) and \(\mathbf{1}\) is \(\mathsf{void}\).
- The isomorphism \(\lambda\) is the set of functions
  \[\{\lambda(x:\tau)\ .\ (\mathsf{inj}\ x=R\ \mathsf{as}\ \mathsf{void}+\tau)|\tau\in\mathrm{Ob}(\mathcal{T})\}.\]

  Its inverse are a bit involved because we need to create an object of the target type from the void for the left branch, even though it's impossible to enter the branch. This can be derived recursively:
  - For \(\tau=\mathsf{void}\), its inverse is
    \[\lambda(x:\mathsf{void}+\mathsf{void})\ .\ \mathsf{case}\ e\ \{L(x_L) \to x_L\ \mid\ R(x_R) \to x_R\}.\]
  - For \(\tau=\mathsf{unit}\), its inverse is
    \[\lambda(x:\mathsf{void}+\mathsf{unit})\ .\ \mathsf{case}\ e\ \{L(x_L) \to ()\ \mid\ R(x_R) \to x_R\}.\]
  - If the inverse for \(\tau_1,\tau_2\) are \(\lambda^{-1}_{\tau_1},\lambda^{-1}_{\tau_2}\) respectively, then the inverses are:
    \[\lambda(x:\mathsf{void}+(\tau_1\times\tau_2))\ .\ \mathsf{case}\ e\ \{L(x_L) \to (\lambda^{-1}_{\tau_1}(x_L),\lambda^{-1}_{\tau_2}(x_L))\ \mid\ R(x_R) \to x_R\}.\]
    \[\lambda(x:\mathsf{void}+(\tau_1\to\tau_2))\ .\ \mathsf{case}\ e\ \{L(x_L) \to (\lambda(x:\tau_1)\ .\ \lambda^{-1}_{\tau_2}(x_L))\ \mid\ R(x_R) \to x_R\}.\]
    \[\lambda(x:\mathsf{void}+(\tau_1+\tau_2))\ .\ \mathsf{case}\ e\ \{L(x_L) \to (\mathsf{inj}\ \lambda^{-1}_{\tau_1}(x_L)=L\ \mathsf{as}\ \tau_1+\tau_2)\ \mid\ R(x_R) \to x_R\}.\]

  The isomorphism \(\rho\) can be defined in similar way.
- \(\alpha\) is a set of functions
  \[\{f_{\tau_1,\tau_2,\tau_3}:(\tau_1\times\tau_2)\times\tau_3\to\tau_1\times(\tau_2\times\tau_3)|\tau_1,\tau_2,\tau_3\in\mathrm{Ob}(\mathcal{T})\},\]
  where \(f_{\tau_1,\tau_2,\tau_3}\) matches every case in \((\tau_1\times\tau_2)\times\tau_3\) and inject it as \(\tau_1\times(\tau_2\times\tau_3)\).

## Closing thoughts

So far, we have understood that there are a CCC and a monoidal structure inside simply typed lambda calculus. The goal of this post is
1. to create a linear type system by adding constraints to the type system,
2. prove that it's a monoidal category, and
3. using diagrams (e.g. the wiring diagram in the [chapter 2 of the *Seven Sketches* book](https://arxiv.org/abs/1803.05316)) to visualize linear type systems.

However, I'm still not sure whether the first step is doable.

## Appendix: The Real Proof of \ref{ex:type-ccc}

Before proving it, we need to address the problem of equivalence because things like "unique" and "commute" in the requirements need a clear definition of "two lambdas[^lambda] being equal". Consider these question:
- Does \(\lambda(x:\tau)\ .\ x\) equal to \(\lambda(y:\tau)\ .\ y\)?
- Does \(\lambda(x:\mathsf{unit})\ .\ x\) equal to \(\lambda(x:\mathsf{unit})\ .\ \mathsf{unit}\)?

[^lambda]: I'll use lambda to denote functions in lambda calculus here to distinguish it from functions in \(\mathsf{Set}\). The latter will just be called "function"

One possible definition is that: a lambda defines a function in \(\mathsf{Set}\), so two lambdas are equal if the underlying functions are equal. Using this definition, both questions above are true.

Back to the claims in \ref{ex:type-ccc}:
> There is a \(\mathsf{unit}\) type that for every type \(\tau\), there is exactly one function \(\lambda(x:\tau)\ .\ ()\) with type \(\tau\to\mathsf{unit}\).

That's because the underlying function is unique, which is proved in \ref{ex:set-ccc}.

> For every type \(\tau\), the right adjoint to \(-\times\tau\) is \(-^\tau\), where \(\tau_1^{\tau_2}\) is the type of function \(\tau_2\to\tau_1\).

You can copy the adjunction claim in \ref{ex:set-ccc} and rewrite it using the language of lambda calculus. The underlying function remains unchanged.

Here are some alternative definitions of being equal. It will be interesting to see (and much harder to check) if the type system is still CCC under these definitions:
- Programs can be represented by their strings. Two lambdas are equal iff their strings are equal. Both of the questions above are false when using this definition.
- Two lambdas are equal iff they are alpha-equivalent, i.e. you convert them into [DeBruijn index](https://en.wikipedia.org/wiki/De_Bruijn_index) and they become the same string. Then the answer to the first question is yes and the second is no.

