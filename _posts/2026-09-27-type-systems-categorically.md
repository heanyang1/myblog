---
layout: post
title:  "Understanding Type Systems with Category Theory"
---

In the beginning of [the assignments 6 of Stanford CS242](https://stanford-cs242.github.io/f19/assignments/assign6/), there is a quote from [linear logic's Wikipedia page](https://en.wikipedia.org/wiki/Linear_logic):
> "In terms of simple denotational models, linear logic may be seen as refining the interpretation of intuitionistic logic by replacing cartesian (closed) categories by symmetric monoidal (closed) categories ..."

This feels like an abstract nonsense to me when learning CS242, but after learning some basics of category theory, I realized that this does capture the essence of linear types. In fact, I think symmetric monoidal closed categories is *the only correct way* to understand linear type systems like the one in Rust [^lambda_quote].

[^lambda_quote]: There is [a similar claim](https://math.ucr.edu/home/baez/act_course/lecture_2.html) by John Baez that he can only understand lambda calculus via (probably cartesian closed) categories.

In this post, I'll try to decipher the sentence so it can be digested by us mortals. I'll assume that you are familiar with the concepts in [my previous post about category theory](/myblog/2026/08/09/dfa-with-category-theory.html).

## The Language

A subset of the typed lambda calculus in CS242 will be used throughout the post [^ocr]:
\[\begin{aligned}
\mathsf{Type}~\tau \ ::={} & \mathsf{unit} \\
& \mid\;\ \mathsf{int} \\
& \mid\;\ \tau_{arg} \to \tau_{ret} \\
& \mid\;\ \tau_L \times \tau_R \\[2ex]
\mathsf{Expression}~e \ ::={} & x \\
& \mid\;\ n \\
& \mid\;\ e_L\oplus e_R \\
& \mid\;\ \lambda\ (x:\tau)\,.\ e \\
& \mid\;\ e_{lam}\ e_{arg} \\
& \mid\;\ () \\
& \mid\;\ (e_L,\ e_R) \\
& \mid\;\ e\,.\,d \\[2ex]
\mathsf{Direction}~d \ ::={} & L\;\mid\;R \\[2ex]
\mathsf{Binop}~\oplus \ ::={} & +\;\mid\;-\;\mid\;*\;\mid\;/
\end{aligned}\]
\[\dfrac{}
      {\Gamma \vdash n : \mathsf{int}}~~\text{(T-Num)}
\qquad
\dfrac{\Gamma \vdash e_L : \mathsf{int}\qquad\Gamma \vdash e_R : \mathsf{int}}
      {\Gamma \vdash e_L\oplus e_R : \mathsf{int}}~~\text{(T-Binop)}
\]
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

[^ocr]: (a) The grammar is OCRed from a screenshot taken from CS242's assignment 4, (b) some trivial typing rules are omitted.

We are interested in the following properties of the language:
1. There is a \(\mathsf{unit}\) type with exactly one element `()`, and for every type \(\tau\) you can construct a function \(\tau\to\mathsf{unit}\) by returning `()`.
2. For every types \(\tau_1,\tau_2\), we can construct a pair with type \((\tau_1,\tau_2)\) and function with type \(\tau_1\to\tau_2\).
3. Currying \(\tau_1\to(\tau_2\to\tau_3)\Leftrightarrow(\tau_1\times\tau_2)\to\tau_3\) allow us to transform function types to product types and vice versa.

These 3 properties makes the type system a *cartesian closed category*.

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

## Linear Types

Now suppose that we have added some primitive functions to the language:
- \(\mathsf{read}:\mathsf{int}\to\mathsf{int}\) uses the input as address and returns the memory's value of that address. For simplicity, we can only read/write integers.
- \(\mathsf{write}:\mathsf{int}\to\mathsf{int}\to\mathsf{unit}\) inputs an address and a value, write the value to the memory,
- \(\mathsf{spawn}:(\mathsf{unit}\to\mathsf{unit})\to\mathsf{unit}\) creates a thread that runs the input function.

Then the language is dangerous enough to create a data race:
```
(λ (p: int × int) .
    (spawn (λ (_: unit) . write p.L 1),
     spawn (λ (_: unit) . write p.R 2)))
```

The problem is that integer variables are too expressive to be used as addresses. The memory cell behind an address should be read or written by only one thread, whereas an integer variable is copied and used by two threads in the example.

In the [Linear Types can Change the World! paper](https://www.semanticscholar.org/paper/Linear-Types-can-Change-the-World%21-Wadler/24c850390fba27fc6f3241cb34ce7bc6f3765627?p2df), Philip Wadler designed a *linear type system* where you can not copy or discard a variable. We can use the paper's idea to make our type system linear.

First, typing rules are changed so an item in the context can only be used exactly once:
\[\dfrac{}
      {\varnothing \vdash n : \mathsf{int}}~~\text{(T-Num-Linear)}
\qquad
\dfrac{\Gamma_1 \vdash e_L : \mathsf{int}\qquad\Gamma_2 \vdash e_R : \mathsf{int}}
      {\Gamma_1,\Gamma_2 \vdash e_L\oplus e_R : \mathsf{int}}~~\text{(T-Binop-Linear)}
\]
\[\dfrac{\Gamma_1 \vdash e_{lam} : \tau_{arg} \to \tau_{ret} \qquad \Gamma_2 \vdash e_{arg} : \tau_{arg}}
      {\Gamma_1,\Gamma_2 \vdash (e_{lam}\ e_{arg}) : \tau_{ret}}~~\text{(T-App-Linear)}\]
\[\dfrac{}{x : \tau \vdash x : \tau}~~\text{(T-Var-Linear)}\quad\dfrac{}{\varnothing\vdash () : \mathsf{unit}}~~\text{(T-Unit-Linear)}\]
\[\dfrac{\Gamma_1 \vdash e_L : \tau_L \qquad \Gamma_2 \vdash e_R : \tau_R}
      {\Gamma_1,\Gamma_2 \vdash (e_L,\ e_R) : \tau_L \times \tau_R}~~\text{(T-Pair-Linear)}\]
where \(\Gamma_1,\Gamma_2\) is the disjoint union of sets \(\Gamma_1,\Gamma_2\).

Second, the \(e.L\) and \(e.R\) syntax are replaced by a syntax that doesn't allow you to discard the other side of the pair:
\[\begin{aligned}
\mathsf{Expression}~e \ ::={} & \dots \\
& \mid\;\ \mathsf{unpack}\ p\ \mathsf{as}\ (l,r)\ \mathsf{in}\ e \\
\end{aligned}\]
\[\dfrac{\Gamma_1 \vdash p : \tau_L \times \tau_R \qquad \Gamma_2,l:\tau_L,r:\tau_R\vdash e:\tau_e}{\Gamma_1,\Gamma_2 \vdash \mathsf{unpack}\ p\ \mathsf{as}\ (l,r)\ \mathsf{in}\ e:\tau_e}~~\text{(T-Unpack)}
\]

For reasons that won't be clear until next section, we allow removing variables with type \(\mathsf{unit}\) from the context through a special syntax:
\[\begin{aligned}
\mathsf{Expression}~e \ ::={} & \dots \\
& \mid\;\ \mathsf{discard}\ u\ \mathsf{in}\ e \\
\end{aligned}\]
\[\dfrac{\Gamma_1 \vdash u : \mathsf{unit} \qquad \Gamma_2\vdash e:\tau_e}{\Gamma_1,\Gamma_2 \vdash \mathsf{discard}\ u\ \mathsf{in}\ e:\tau_e}~~\text{(T-Discard)}
\]

The following example shows that linear type systems disallow us to copy arbitrary variables.

**Example.**\label{ex:linear-no-copy} The function \(\lambda(x:\mathsf{int})\ .\ (x,x)\) won't type check in the linear type system.

To check its type, we need to use (T-Lam-Linear) which adds \(x:\mathsf{int}\) to the context, and (T-Pair-Linear) which splits the context into two halves. The item \(x:\mathsf{int}\) can't be in both halves, and you can't check \(x\)'s type with the part that doesn't contain \(x:\mathsf{int}\).

Assume that there are no primitives like the \(\mathsf{read}\) or \(\mathsf{write}\) mentioned above, then we can prove that the linear type system equipped with \(\times\) and \(\mathsf{unit}\) (denoted as \((\mathcal{L},\times,\mathsf{unit})\)) is not a CCC. The proof is a bit hard and not so relevant to the topic, so I'll put it in the appendix.

## Monoidal Category

Although \((\mathcal{L},\times,\mathsf{unit})\) is not a CCC, it is a *symmetric monoidal (closed) category*, and it's good enough to describe the behaviour of the variables.

**Definition.**\label{def:monoidal-category} A *monoidal (closed) category* contains following items:
1. a category \(\mathcal{V}\),
2. a bifunctor \(\otimes:\mathcal{V}\times\mathcal{V}\to\mathcal{V}\),
3. an object \(\mathbf{1}\) in \(\mathcal{V}\) such that \(\mathbf{1}\otimes*:\mathcal{V}\to\mathcal{V}\) (denoted as \(\lambda\)) and \(*\otimes\mathbf{1}:\mathcal{V}\to\mathcal{V}\) (denoted as \(\rho\)) are natural isomorphisms,
4. a natural isomorphism \(\alpha\) on the category of functors \(\mathcal{V}\times\mathcal{V}\times\mathcal{V}\to\mathcal{V}\) that maps \((*\otimes*)\otimes *\) to \(*\otimes(*\otimes*)\), such that the following diagrams commute:

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
\draw[->] (top)  -- node[above left]  {$\alpha_{X,Y,Z}\otimes\mathrm{id}_W$} (lmid);
\draw[->] (top)  -- node[above right] {$\alpha_{X\otimes Y,Z,W}$} (rmid);
\draw[->] (lmid) -- node[left]        {$\alpha_{X,Y\otimes Z,W}$} (lbot);
\draw[->] (rmid) -- node[right]       {$\alpha_{X,Y,Z\otimes W}$} (rbot);
\draw[->] (lbot) -- node[below]       {$\mathrm{id}_X\otimes\alpha_{Y,Z,W}$} (rbot);
\end{tikzpicture}
\end{document}
```

```tikz
\documentclass[tikz]{standalone}
\usepackage{amsmath,amssymb}
\begin{document}
\begin{tikzpicture}
  \node (tl)   at (-2,1.7)    {$A\otimes(\mathbf{1}\otimes B)$};
  \node (tr)  at (2,1.7)  {$(A\otimes \mathbf{1})\otimes B$};
  \node (bot)  at (0,0)      {$A\otimes B$};
  \draw[->] (tl) to node[above] {$\alpha_{A,\mathbf{1},B}$} (tr);
  \draw[->] (tl) to node[left] {$\mathrm{id}_A\otimes\lambda_B$} (bot);
  \draw[->] (tr) to node[right] {$\rho_A\otimes\mathrm{id}_B$} (bot);
\end{tikzpicture}
\end{document}
```

The monoidal category is *symmetric* if there is an isomorphism \(\sigma\) on the category of bifunctors \(\mathcal{V}\times\mathcal{V}\to\mathcal{V}\) that maps \((X,Y)\to X\otimes Y\) to \((X,Y)\to Y\otimes X\), such that there are some more diagrams [^omitted] commute.

[^omitted]: The diagrams can be found [here](https://en.wikipedia.org/wiki/Symmetric_monoidal_category#Definition).

If you still remember what lattice is, then you will recognize that complete lattices are monoidal categories:

**Example.**\label{ex:lattices-monoidal} When viewed as a thin category, a lattice \(L\) is a symmetric monoidal category. There are two monoidal structures \((\sqcup,\perp)\) and \((\sqcap,\top)\) in \(L\).

The following proposition show that the requirements of CCC is stronger than that of monoidal category.

**Proposition.**\label{prop:ccc-monoidal} If a category \(\mathcal{C}\) is a CCC, then it is also a symmetric monoidal category. Its \(\otimes\) is the product \(\times\), its \(\mathbf{1}\) is the terminal object.

By definition of product:
1. For every object \(X\) in \(\mathcal{C}\), there is a morphism \(\lambda_{X}:\mathbf{1}\times X\to X\).
2. For every object \(Y\) in \(\mathcal{C}\), there is always a morphism \(Y\to\mathbf{1}\), so if there is a morphism \(g:Y\to X\), then there is a unique morphism \(f:Y\to\mathbf{1}\times X\) such that \(g=\lambda_{X}\circ f\).
   - Let \(Y=X\) and \(g=\mathrm{id}_X\), then we have a unique morphism \(h_X\) such that \(\mathrm{id}_{X}=\lambda_{X}\circ h_X\).
   - Let \(Y=\mathbf{1}\times X\) and \(g=\lambda_X\), then we have a unique morphism \(h:\mathbf{1}\times X\to\mathbf{1}\times X\) such that \(\lambda_X=\lambda_X\circ h\).

     Because \(\lambda_X=\lambda_X\circ\mathrm{id}_{\mathbf{1}\times X}\), therefore \(h=\mathrm{id}_{\mathbf{1}\times X}\).

     Because \(\lambda_X\circ(h_X\circ \lambda_X)=(\lambda_X\circ h_X)\circ \lambda_X=\mathrm{id}_{X}\circ\lambda_X=\lambda_X\), therefore \(h_X\circ \lambda_X=\mathrm{id}_{\mathbf{1}\times X}\).

Therefore \(\mathbf{1}\times *\) is isomorphism.

Because for every morphism \(f:X\to Y\) in \(\mathcal{C}\), the diagram
\[
\begin{CD}
\mathbf{1}\times X @>\lambda_{X}>> X \\
@V\mathrm{id}_{\mathbf{1}}\times fVV @VVfV \\
\mathbf{1}\times Y @>\lambda_{Y}>> Y \\
\end{CD}
\]
commutes, therefore \(\mathbf{1}\times*\) is a natural isomorphism. Similarly \(*\times\mathbf{1}\) is natural isomorphism.

For every object \(X,Y,Z\) in \(\mathcal{C}\), consider the object \((X\times Y)\times Z\):
1. There is a morphism from \((X\times Y)\times Z\) to \(X,Y,Z\) respectively.
2. If there is an object \(W\) with morphism \(W\to X,W\to Y,W\to Z\), then by definition of product, there's also a morphism \(W\to(X\times Y)\), therefore there's a unique morphism \(W\to((X\times Y)\times Z)\).

Therefore \((X\times Y)\times Z=\prod\{X,Y,Z\}\). Similarly, \(X\times(Y\times Z)=\prod\{X,Y,Z\}\). Because products are unique upto isomorphism, therefore \((X\times Y)\times Z\cong X\times(Y\times Z)\). This gives us \(\alpha\).

Now we need to prove that for every morphism \(f:(X_1,Y_1,Z_1)\to(X_2,Y_2,Z_2)\) in \(\mathcal{C}\times\mathcal{C}\times\mathcal{C}\), the following square commutes:
\[
\begin{CD}
(X_1\times Y_1)\times Z_1 @>\alpha_{X_1,Y_1,Z_1}>> X_1\times (Y_1\times Z_1) \\
@V((*\times *)\times *)fVV @VV(*\times (*\times *))fV \\
(X_2\times Y_2)\times Z_2 @>\alpha_{X_2,Y_2,Z_2}>> X_2\times (Y_2\times Z_2) \\
\end{CD}\tag{eq:ccc-monoidal-commute}
\]

The commute proof of this diagram as well as the pentagonal diagram, trianglar diagram and hexagonal diagram in the symmetric definition are trivial, if not tedious. \(\Box\)

**Example.**\label{ex:linear-monoidal} Our linear type system \(\mathcal{L}\) is a symmetric monoidal category.
- Its \(\otimes\) is the product \(\times\) and its \(\mathbf{1}\) is \(\mathsf{unit}\).
- For every type \(\tau\), \(\lambda_{\tau}\) is
  \[\lambda(x:\mathsf{unit}\times\tau)\ .\ \mathsf{unpack}\ x\ \mathsf{as}\ (l,r)\ \mathsf{in}\ (\mathsf{discard}\ l\ \mathsf{in}\ r),\]
  and its inverse is \(\lambda(x:\tau)\ .\ ((), x)\). \(\rho\) can be defined in similar ways.
- For every types \(\tau_1,\tau_2,\tau_3\), we can define \(\alpha\) as
  \[\lambda(x:(\tau_1\times\tau_2)\times\tau_3)\ .\ \mathsf{unpack}\ x\ \mathsf{as}\ (l,r)\ \mathsf{in}\ (\mathsf{unpack}\ l\ \mathsf{as}\ (ll,lr)\ \mathsf{in} (ll, (lr, r))).\]
- For every type \(\tau_1,\tau_2\), \(\sigma_{\tau_1,\tau_2}\) is \[\lambda(x:\tau_1\times\tau_2)\ .\ \mathsf{unpack}\ x\ \mathsf{as}\ (l,r)\ \mathsf{in}\ (r,l).\]

The proof that \(\alpha\) is natural and the pentagonal diagram commutes is trivial, if not tedious.

## Aside: Sum Types

We can add more monoidal structure to the type system. For example, adding sum types
\[\begin{aligned}
\mathsf{Type}~\tau \ ::={} & \dots \\
& \mid\;\ \tau_L + \tau_R \\[2ex]
\mathsf{Expression}~e \ ::={} & \dots \\
& \mid\;\ \mathsf{inj}\ e = d\ \mathsf{as}\ \tau \\
& \mid\;\ \mathsf{case}\ e\ \{L(x_L) \to e_L\ \mid\ R(x_R) \to e_R\} \\
\end{aligned}\]
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
to the language forms an monoidal category:
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
- For every type \(\tau_1,\tau_2,\tau_3\), \(\alpha_{\tau_1,\tau_2,\tau_3}\) is
  ```
  λ (x : (τ1​ + τ2​) + τ3) .
    case x {
      L(l) -> case l {
        L(ll) -> inj ll = L as τ1​ + (τ2​ + τ3),
        L(lr) -> inj (inj lr = L as τ2​ + τ3) = R as τ1​ + (τ2​ + τ3)
      },
      R(r) -> inj (inj r = R as τ2​ + τ3) = R as τ1​ + (τ2​ + τ3)
    }
  ```
- For every type \(\tau_1,\tau_2\), \(\sigma_{\tau_1,\tau_2}\) is
  ```
  λ (x : τ1​ + τ2​) .
    case x {
      L(l) -> inj l = R as τ1​ + τ2​,
      R(r) -> inj r = L as τ1​ + τ2
    }
  ```

The proof that \(\alpha\) is natural and the pentagonal diagram commutes is trivial, if not tedious.

## Closing thoughts

To summarize:
- Simply typed lambda calculus forms a CCC.
- We add some constraints to simply typed lambda calculus so most variables can't be copied or discarded. The resulting type system becomes linear.
- Linear type systems are no longer CCC, so we instead model it as a symmetric monoidal category. This is what the quote in the beginning says.

This post is not finished yet. I'm planning to introduce diagrams (e.g. the wiring diagram in the [chapter 2 of the *Seven Sketches* book](https://arxiv.org/abs/1803.05316)) to visualize monoidal category so you'll understand why I think monoidal categories capture the essence of linear type systems.

## Appendix A: The Real Proof of \ref{ex:type-ccc}

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

## Appendix B: Linear Type System is not CCC

> The idea of the proof is given by AI. The original formalized proof is available [here](https://github.com/heanyang1/proofs/blob/main/Proofs/TypeSystems_2026_09_27.lean). The proof in the post is hand written with the exception that the table is AI-drawn.

The plan is to prove that we can't construct certain types within an empty context, including the type \(\mathsf{int}\to\mathsf{unit}\), so \(\mathsf{unit}\) is not the terminal object of the type system.

The proof is inspired by the *phase semantics* in [Girard's paper](https://girard.perso.math.cnrs.fr/linear.pdf), so reading the paper or [this more accessable introduction](https://www.cs.brandeis.edu/~cs112/2006-cs112/docs/girard-intro.pdf) may be beneficial (although not required) to understand the proof.

We define a function \(\mathrm{ph}(\tau)\) (\(\mathrm{ph}\) stands for *phase*) that maps every type to a subset of \(\mathbb{N}\): [^explain]
- \(\mathrm{ph}(\mathsf{unit})=\{0\}\),
- \(\mathrm{ph}(\mathsf{int})=\mathbb{N}\),
- \(\mathrm{ph}(\tau_1\times\tau_2)=\{x+y|x\in\mathrm{ph}(\tau_1),y\in\mathrm{ph}(\tau_2)\}\),
- \(\mathrm{ph}(\tau_1\to\tau_2)=\{y|\forall x\in\mathrm{ph}(\tau_1),x+y\in\mathrm{ph}(\tau_2)\}\).

[^explain]: Here's an explaination for those who have read Girard's paper: We use \((\mathbb{N},+,0)\) as the monoid and \(\perp=\{0\}\) to construct the phase space of the linear language. The proof will be very similar to the provability proof of linear logic.

For a non-empty context \(\Gamma=\tau_1,\dots,\tau_n\), \(\mathrm{ph}(\Gamma)=\bigcup_{i=1}^n\mathrm{ph}(\tau_i)\), and \(\mathrm{ph}(\Gamma)=\{0\}\) if \(\Gamma\) is empty.

The expression of \(\mathrm{ph}(\tau_1+\tau_2)\) and \(\mathrm{ph}(\tau_1\to\tau_2)\) are actually very simple because the following lemma shows that we can only assign \(\varnothing,\{0\},\mathbb{N}\) to the types, and there are only 9 possible results of the operations:

**Lemma.**\label{lem:simple-subset} For every type \(\tau\), \(\mathrm{ph}(\tau)\) can only be one of the \(\varnothing,\{0\},\mathbb{N}\).

*proof.* Using structural induction over \(\tau\):
- Base case: \(\mathrm{ph}(\mathsf{unit})=\{0\}\) and \(\mathrm{ph}(\mathsf{int})=\mathbb{N}\).
- Assume \(\tau_1,\tau_2\) are among \(\varnothing,\{0\},\mathbb{N}\), then we can draw the table of \(\mathrm{ph}(\tau_1\times\tau_2)\) and \(\mathrm{ph}(\tau_1\to\tau_2)\) as follows:
  \[
  \begin{array}{c|ccc}
  \times & \varnothing & \{0\} & \mathbb{N}\\\hline
  \varnothing & \varnothing & \varnothing & \varnothing\\
  \{0\} & \varnothing & \{0\} & \mathbb{N}\\
  \mathbb{N} & \varnothing & \mathbb{N} & \mathbb{N}
  \end{array}
  \qquad\qquad
  \begin{array}{c|ccc}
  \to & \varnothing & \{0\} & \mathbb{N}\\\hline
  \varnothing & \mathbb{N} & \mathbb{N} & \mathbb{N}\\
  \{0\} & \varnothing & \{0\} & \mathbb{N}\\
  \mathbb{N} & \varnothing & \varnothing & \mathbb{N}
  \end{array}\tag{eq:phase-table}
  \]

  where the rows are \(\mathrm{ph}(\tau_1)\) and the columns are \(\mathrm{ph}(\tau_2)\). The row \(\varnothing\) of the second table is all \(\mathbb{N}\) because the condition \(\forall x\in\varnothing\) is vacuously satisfied. \(\Box\)

Here's the main result:

**Proposition.**\label{prop:derivable} A type checking statement \(\Gamma\vdash e:\tau\) is correct only if \(\mathrm{ph}(\Gamma)\subseteq\mathrm{ph}(\tau)\).

*proof.* Using structural induction over \(e\):

(T-Num-Linear) \(\mathrm{ph}(\Gamma)=\{0\}\subseteq\mathbb{N}=\mathrm{ph}(\tau)\).

(T-Binop-Linear) Assume that \(\mathrm{ph}(\Gamma_1)\subseteq\mathrm{ph}(\mathsf{int})=\mathbb{N}\) and \(\mathrm{ph}(\Gamma_2)\subseteq\mathrm{ph}(\mathsf{int})=\mathbb{N}\), then
\[\mathrm{ph}(\Gamma_1)\cup\mathrm{ph}(\Gamma_2)\subseteq\mathbb{N}=\mathrm{ph}(\mathsf{int}).\]

(T-Lam) Assume that \(\mathrm{ph}(\Gamma)\cup\mathrm{ph}(\tau_{arg})\subseteq\mathrm{ph}(\tau_{ret})\). Using the tables in \ref{eq:phase-table}, we can verify that \(\mathrm{ph}(\Gamma)\subseteq\mathrm{ph}(\tau_{arg}\to\tau_{ret})\).

(T-Unpack) Assume that \(\mathrm{ph}(\Gamma_1)\subseteq\mathrm{ph}(\tau_L\times\tau_R)\) and \(\mathrm{ph}(\Gamma_2)\cup\mathrm{ph}(\tau_{L})\cup\mathrm{ph}(\tau_{R})\subseteq\mathrm{ph}(\tau_{e})\).

If \(\mathrm{ph}(\tau_{e})=\varnothing\), then \(\mathrm{ph}(\Gamma_2),\mathrm{ph}(\tau_{L}),\mathrm{ph}(\tau_{R})\) are \(\varnothing\) by the second assumption, then \(\mathrm{ph}(\Gamma_1)=\varnothing\) by the first assumption, so
\[\mathrm{ph}(\Gamma_1)\cup\mathrm{ph}(\Gamma_1)\subseteq\mathrm{ph}(\tau_e).\tag{eq:unpack-result}\]

If \(\mathrm{ph}(\tau_{e})=\{0\}\), then \(\mathrm{ph}(\Gamma_2),\mathrm{ph}(\tau_{L}),\mathrm{ph}(\tau_{R})\) can not be \(\mathbb{N}\) by the second assumption, then \(\Gamma_1\) can not be \(\mathbb{N}\) by the first assumption, and the equation \ref{eq:unpack-result} holds.

If \(\mathrm{ph}(\tau_{e})=\mathbb{N}\), then the equation \ref{eq:unpack-result} holds because \(\mathrm{ph}(\tau)\subseteq\mathbb{N}\) for every \(\tau\).

Other rules are similar to the rules above. \(\Box\)

Because \(\mathrm{ph}(\mathsf{int}\to\mathsf{unit})=\varnothing\), therefore it's impossible to check the type using an empty context whose phase is \(\{0\}\).

