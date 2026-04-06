---
layout: post
title:  "Solving \"Lights Out\" Puzzles"
---

The [Racket programming language](https://racket-lang.org/) has a dozen of simple [bundled games](https://pkgs.racket-lang.org/package/games), one of which is the "Lights Out" puzzles. Here is the screenshot of the game and its instructions:
![game](/myblog/assets/2026-04-06/lights-out.png)

It's supposed to be a hard game if you are using your human heuristics or logic (or luck?), but this game can actually be solved using a dumb polynomial algorithm, and you probably have learned it in your linear algebra class.

## The Problem

Let's consider a generalized problem: we are playing "Lights out" on an undirected simple graph (i.e. there is at most one edge between two nodes), and clicking a node also toggles lights of its neighbors. Our goal is to turn off all the lights in the graph.

Here's an example of 6 nodes \(a,b,c,d,e,f\):
![example](/myblog/assets/2026-04-06/example.png)

If you want to play the generalized game and gain some intuition, here's an [app](https://github.com/heanyang1/graph-drawing) written specifically for this blog post. Roughly 90% of the code and every line of the document is written by a coding agent. See Appendix A for its technical details.

## The Solution

Suppose that we have known the solution to the above example. Let \(a'\) be the number of clicks on node \(a\), \(b'\) be the number of clicks on node \(b'\), etc. Then we can have a set of equations by examine each node and its neighbors:
\[\begin{cases}
(a'+d')\mathrm{mod}\ 2=0, \\
(b'+d'+e'+f')\mathrm{mod}\ 2=1, \\
(c'+f')\mathrm{mod}\ 2=0, \\
(d'+a'+b')\mathrm{mod}\ 2=1, \\
(e'+b'+f')\mathrm{mod}\ 2=0, \\
(f'+b'+c'+e')\mathrm{mod}\ 2=1. \\
\end{cases}\tag{1}\]

The first equation can be obtained by looking at the node \(a\). It should remain off, so it should be toggled by even number of times. Its neighbors are node \(d\), and any click to itself and its neighbors will toggle it once, so it will be toggled \(a'+d'\) times. The same is true for the node \(b\), except that it should be turned off by toggling odd number of times, this gives us the \(1\) in the right-hand side of the second equation.

Note that all the parameters are in \(\mathbb{Z}_2\) (because of the simple graph constraint), therefore we can get rid of the annoying \(\text{mod}\ 2\) by solving the equations (1) in the field \((\mathbb{Z}_2,+,\cdot)\):
\[\begin{cases}
a'+d'=0, \\
b'+d'+e'+f'=1, \\
c'+f'=0, \\
d'+a'+b'=1, \\
e'+b'+f'=0, \\
f'+b'+c'+e'=1. \\
\end{cases}(a',b',c',d',e',f'\in\mathbb{Z}_2)\tag{2}\]

In fact, (as shown in Appendix B) we won't miss any solution by limiting the scope: if there is no solution on \(\mathbb{Z}_2\), neither will there be a solution on \(\mathbb{Z}\).

So it's just a set of linear equations which can be solved by [Gaussian elimination](https://en.wikipedia.org/wiki/Gaussian_elimination). It's even simpler since we are doing Gaussian elimination on \(\mathbb{Z}_2\).

Here's the algorithm that can solves any light-out puzzle:
1. Get the adjacent matrix \(A\) and the vector \(Y=(y_1,\dots,y_m)\), where \(y_i=1\) if the i-th node is on, otherwise \(y_i=0\).
2. Solve the set of equations \((A+I)X=Y\) on \(\mathbb{Z}_2\). If it's unsolvable, then the puzzle is not solvable.

I [implemented the algorithm in the app](https://github.com/heanyang1/graph-drawing/blob/main/src/gaussian_elimination.rs) so that the app can show you the solution if there is any. The algorithm is boring, so I won't paste it here to waste your time (although it's written by hand, and it's about 80 lines of code).

## Conclusion

Perhaps the game is too simple to write a blog post to solve it, but it's a interesting game anyway. I thought that a puzzle game must be NP-hard to be hard enough for humans, but a game that has a simple but unintuitive solution can also be hard.

## Appendix A: Implementation Details of the App

The app is written in Rust using [raylib's Rust binding](https://crates.io/crates/raylib). I chose raylib because I can really understand the code and fix it when something went wrong.

At the time this post is written, [opencode](https://opencode.ai/) is still providing [free models](https://opencode.ai/docs/zen#pricing), so I'm using them for this app.

The project is more challenging than expected as
1. It's a GUI app and is hard to test.
2. I decided to start with something small and gradually adding features to it.
3. The agent tends to patch things up instead of refactor the code when the old design is not suitable for a new feature.
4. As a result, technical debt accumulates, and you will get an unmaintainable, buggy app.
5. This gets worse when the agent has to compress the context and most of its experience are lost.

Maybe I should add something like "Refactor the code when it smells" to the agent's skills, but I doubt that it has the correct judgment. I'll try that in later projects.

## Appendix B: Why Solving in \(\mathbb{Z}_2\)

Let's proof its converse: let \(A=(a_{ij})\) be an \(m\times n\) matrix on \(\mathbb{Z}_2\) and \(Y\) be a vector in \((\mathbb{Z}_2)^m\), then if \((AX)\text{mod}\ 2=Y\) has solution \(X'\in\mathbb{Z}^n\), the equation \(AX=Y\) has solution in \((\mathbb{Z}_2)^n\).

Let \(f:\mathbb{Z}\to\mathbb{Z},f(x)=x\ \mathrm{mod}\ 2\). Because for every \(x,y\in\mathbb{Z}\), \(f(x+y)=f(x)+f(y)\), \(f(xy)=f(x)f(y)\) and \(f(0)=0\), therefore \(f\) is a homomorphism between the ring \(\mathbb{Z}\) and \(\mathbb{Z}_2\).

Let \(X'=(x_1,\dots,x_n)\), \(Y=(y_1,\dots,y_m)\), then \(AX\text{mod}\ 2=Y\) can be expanded as:
\[\begin{cases}
f(a_{11}x_1+a_{12}x_2+\cdots+a_{1n}x_n)=y_1, \\
\cdots, \\
f(a_{m1}x_1+a_{m2}x_2+\cdots+a_{mn}x_n)=y_m. \\
\end{cases}\]

Because \(f\) is homomorphism, we have
\[\begin{cases}
f(a_{11})f(x_1)+f(a_{12})f(x_2)+\cdots+f(a_{1n})f(x_n)=y_1, \\
\cdots, \\
f(a_{m1})f(x_1)+f(a_{m2})f(x_2)+\cdots+f(a_{mn})f(x_n)=y_m. \\
\end{cases}\]

Since \(a_{ij}\in\mathbb{Z_2}\), therefore \(f(a_{ij})=a_{ij}\). So \((f(x_1),\dots,f(x_n))\in(\mathbb{Z}_2)^n\) is a solution to \(AX=Y\). \(\Box\)

Here's an interpretation of this proposition: you don't need to click a node more than once, since clicking a node twice does nothing.
