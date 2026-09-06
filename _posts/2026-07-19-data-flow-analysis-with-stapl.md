---
layout: post
title:  "Data Flow Analysis with StaPL (Part 1)"
---

> This is the first post of a series about me learning static analysis. Here's [the next post](/myblog/2026/08/09/dfa-with-category-theory.html).
>
> Update on 2026-09-06: I formalized the entire series in Lean using an AI agent, and it found some issues with `/`'s lookup table. Now it's fixed.

Recently I discovered that some parts of my work (I won't share the detail further) are just data flow analysis (DFA) problems. So I read some chapters of [the SPA textbook](https://cs.au.dk/~amoeller/spa/) in the past weekends. The book introduces a language called TIP, with a [C++ compiler and analyzer using LLVM](https://github.com/matthewbdwyer/tipc). Although it may be a good resource for learning LLVM, I don't want to use it now [^tip_later] because
- I need something specifically built for learning DFA, while TIP merges many topics including type inference and pointer analysis.
- I don't think I can understand the codebase in a day.

[^tip_later]: Maybe I'll try it later, after finishing the SPA book and solving the problem at work.

Therefore, I designed StaPL, a small language designed for data flow analysis, and vibe-coded [an interpreter and analyzer](https://github.com/heanyang1/stapl). It's very small, only 1.5k lines of Haskell code in total, so I can understand [^understand] and have full control over every detail despite not writing most of them.

[^understand]: Actually I haven't proofread the entire code base because there is a very large look up table that are too boring to verify. You will see it in later sections.

In this post, I'll walk through the project and introduce some basic concepts of DFA. This post should be self-contained (although it doesn't cover everything in the SPA textbook).

## The Language

You can read the `README.md` of the repo. WARNING: It's AI generated.

For those who don't want to read it: StaPL only contains variable assignments with C-like expressions, conditional jump statements `if e goto l` and IO primitives.

## Control Flow Graph and Program Point

Most DFA are done on the control flow graph (CFG) of the program. In StaPL, each node of the CFG corresponds to a statement, an edge from node `a` to node `b` means that statement `b` may be executed after statement `a`. We use successor map (`cfgSucc`) and predecessor map (`cfgPred`) to represent edges:
```haskell
data CfgNode = CfgNode
  { cfgNodeIndex :: !Int
  , cfgNodeLabel :: !(Maybe Label)
  , cfgNodeStmt  :: !Stmt
  } deriving (Show, Eq, Ord)

data Cfg = Cfg
  { cfgNodes :: !(Map Int CfgNode)
  , cfgSucc  :: !(Map Int [(Int, Maybe Bool)]) -- The `if` statement uses the optional field to decide which branch to go to
  , cfgPred  :: !(Map Int [Int])
  , cfgEntry :: !Int
  } deriving (Show, Eq, Ord)
```

It's useful to have the notion of *program points* besides statements. Imaging a debugger that can execute the StaPL statement one after another, the program point is when the debugger is able to stop. For a statement \(s\), we define two program point \(\mathrm{begin}(s)\) is the point before executing \(s\), and \(\mathrm{end}(s)\) is the point immediately after executing \(s\).

## Sign Analysis

Let's consider a typical static analysis problem: given a program, decide whether its variable is always positive, negative, zero. For example, `x` will always be positive in the following program:
```
x = 1
y = -3
input z
loop: if x > 10 goto end
x = x + 2
y = -y
if 1 goto loop
end: put x
```

The variable `y` can be either positive or negative in the program, so we use a special symbol \(\top\) for the "sign" of `y`, which means "we don't know the sign". The same is true for the variable `z`. We also need a symbol \(\perp\) that indicates that the variable isn't initialized or something goes wrong (e.g. divided by zero or accessing variables that are not existed) when assigning to the variable.

Here's the sign analysis problem described mathematically:
1. We have a program \(\mathcal{P}=\{P,S,V\}\) where \(P\) is the set of program points of the program, \(S\) is the set of statements, and \(V\) is the set of variables.
2. There is also a set of signs \(\mathcal{S}=\{+,-,0,\top,\perp\}\).
3. The goal is to find the *smallest sound* function \(P\to(V\to\mathcal{S})\).

"Smallest" means that there is a partial order \(\{\mathcal{S}^{V^{P}},\sqsubseteq\}\) according to the exactness of the function: in the example above, if \((f(p))(x)=+,(g(p))(x)=\top\) for some program point \(p\), and \(f=g\) everywhere else, then we think \(f\sqsubseteq g\) and we prefer \(f\) over \(g\). As shown in later sections, we don't need to explicitly writing down the partial order to use it.

"Sound" means that the function we want should be *correct* every time we run the program \(\mathcal{P}\). We don't want a function that assigns \(+\) to `z` after `input z` because a user may input `0` and the function will be incorrect. We will leave most of the discussion about the soundness of the algorithm to later posts.

Actually, we don't need to find the function \(P\to(V\to S)\), what we are interested is the value of the function at the end or each statement. Assume that we have found the optimal function \(f\). Let \(S=\{s_1,\dots,s_{|S|}\}\) and \(\sigma_i=f(\mathrm{end}(s_i))\), then finding the vector \(\Sigma=(\sigma_1,\sigma_2,\dots,\sigma_{|S|})\in ({\mathcal{S}}^V)^{|S|}\) is sufficient.

## Lattice

The canonical way to solve DFA problems is to model the partial order as a lattice.

A *partial order* \((A,\sqsubseteq)\) is a set \(A\) and a relation \(\sqsubseteq\) such that:
1. \(\forall a\in A,a\sqsubseteq a\) (reflexivity)
2. \(\forall a_1,a_2,a_3\in A\), if \(a_1\sqsubseteq a_2\) and \(a_2\sqsubseteq a_3\), then \(a_1\sqsubseteq a_3\) (transitivity)
3. \(\forall a_1,a_2\in A\), if \(a_1\sqsubseteq a_2\) and \(a_2\sqsubseteq a_1\), then \(a_1=a_2\) (anti-symmetry)

For a partial order \((A,\sqsubseteq)\) and \(B\subseteq A\), we can define the *join* of \(B\) (denoted as \(\sqcup B\)) as the element \(a\in A\) such that:
1. \(\forall b\in B,b\sqsubseteq a\) (\(a\) is the upper bound).
2. \(\forall a'\in A\), if \(\forall b\in B,b\sqsubseteq a'\), then \(a\sqsubseteq a'\) (\(a\) is the least upper bound).

Similarly, we can define the *meet* of \(B\) (denoted as \(\sqcap B\)) as the greatest lower bound of \(B\).

For a set with two elements \(\{a_1,a_2\}\), we usually use \(a_1\sqcup a_2\) as the join and \(a_1\sqcap a_2\) as the meet.

A *lattice* is a partial order \((A,\sqsubseteq)\) with a \(\sqcup\) and a \(\sqcap\) over every two elements of \(A\). A *complete lattice* is a partial order \((A,\sqsubseteq)\) with a \(\sqcup\) and a \(\sqcap\) over every subset of \(A\).

Finite lattice are always complete lattice since every subset are finite, so you can decompose the join over the subset to pairwise joins.

There are two special elements in a complete lattice \(A\): \(\top:=\sqcup A\) (*top*) and \(\perp:=\sqcap A\) (*bottom*).

In StaPL, the `Lattice` refers to complete lattice:
```haskell
class Ord a => Lattice a where
  elements :: Set a
  bottom :: a
  top    :: a
  join   :: a -> a -> a
  meet   :: a -> a -> a
  leq    :: a -> a -> Bool
```

We can define boolean as lattice:
```haskell
instance Lattice Bool where
  elements = S.fromList [False, True]
  bottom = False
  top    = True
  join   = (||)
  meet   = (&&)
  leq a b = not a || b
```

The power set of a set is also a lattice. To get the information about which set does the current subset belongs to (and to prevent us from accidentally joining two subsets from different sets), we use [Haskell's reflection](https://hackage.haskell.org/package/reflection-2.1.9/docs/Data-Reflection.html) [^haskell_reflection] to encode the set:
```haskell
newtype PowerSet s a = PowerSet { unPowerSet :: Set a }
  deriving (Eq, Ord, Show)

instance (Reifies s (Set a), Ord a) => Lattice (PowerSet s a) where
  elements = S.map PowerSet (S.powerSet (reflect (Proxy @s)))
  bottom   = PowerSet S.empty
  top      = PowerSet (reflect (Proxy @s))
  PowerSet s1 `join` PowerSet s2 = PowerSet (s1 `S.union` s2)
  PowerSet s1 `meet` PowerSet s2 = PowerSet (s1 `S.intersection` s2)
  PowerSet s1 `leq` PowerSet s2 = s1 `S.isSubsetOf` s2
```

[^haskell_reflection]: The mechanism of reflection will probably be the topic of a later post. Now let's just regard it as some weird syntax of Haskell.

We can construct a `PowerSet` like this:
```haskell
import Data.Proxy (Proxy(..))
import Data.Reflection (reify)
import qualified Data.Set as S
import Stapl

main :: IO ()
main = do
  reify (S.fromList [3, 4] :: S.Set Int) $ \ (Proxy :: Proxy s) ->
    let x = bottom :: PowerSet s Int
        y = top :: PowerSet s Int
    in print (x `join` y) -- prints [3, 4]

  reify (S.fromList [1, 2] :: S.Set Int) $ \ (Proxy :: Proxy s1) ->
    reify (S.fromList [3, 4] :: S.Set Int) $ \ (Proxy :: Proxy s2) ->
      let x = bottom :: PowerSet s1 Int
          y = bottom :: PowerSet s2 Int
      in print (x `join` y) -- compile error
```

There are a kind of lattices that are not implemented but needed later: let \(L_1,\dots,L_n\) be lattices, their product \(L_1\times \dots\times L_n\) is also a lattice. For \(X=(x_1,\dots,x_n),Y=(y_1,\dots,y_n)\in L_1\times \dots\times L_n\), \(X\sqsubseteq Y\) iff \(\forall i=1,\dots,n,x_i\sqsubseteq y_i\). Prove that this is indeed a lattice if you are interested.

For a lattice \(L\) and a set \(A\), we can define the *map lattice* \(A\to L\) as follows:
```haskell
newtype MapLattice s k a = MapLattice { unMapLattice :: Map k a }
  deriving (Eq, Ord, Show)

instance (Reifies s (Set k), Ord k, Lattice a) => Lattice (MapLattice s k a) where
  elements =
    let domain = reflect (Proxy @s)
        vals = elements
        allMaps [] _ = S.singleton M.empty
        allMaps (k:ks) vals =
          S.fromList [M.insert k v m | v <- S.toList vals, m <- S.toList (allMaps ks vals)]
    in S.map MapLattice (allMaps (S.toList domain) vals)
  bottom = MapLattice (M.fromSet (const bottom) (reflect (Proxy @s)))
  top    = MapLattice (M.fromSet (const top) (reflect (Proxy @s)))
  -- If an elememt appears in both maps, `unionWith join` will map the key to
  -- the join of the two values, making it a point-wise join.
  MapLattice m1 `join` MapLattice m2 = MapLattice (M.unionWith join m1 m2)
  MapLattice m1 `meet` MapLattice m2 = MapLattice (M.intersectionWith meet m1 m2)
  -- This is similar to product lattice: m1 `leq` m2 iff for every pair `(k, v)` in m1,
  -- `v` is less than the value of `k` in `m2`
  MapLattice m1 `leq` MapLattice m2 =
    all (\ (k, v) -> v `leq` M.findWithDefault bottom k m2) (M.toList m1)
```

The proof that `join` and `meet` are indeed the \(\sqcup\) and \(\sqcap\) in `MapLattice` is left as an exercise for readers.

Returning to the sign analysis example. \(S\) is a lattice:
```haskell
data Sign = Neg | Zero | Pos | Top | Bottom
  deriving (Show, Eq, Ord)

instance Lattice Sign where
  elements = S.fromList [Neg, Zero, Pos, Top, Bottom]
  bottom = Bottom
  top    = Top
  join x y = case (x, y) of
    (Bottom, _) -> y
    (_, Bottom) -> x
    (Top, _)    -> Top
    (_, Top)    -> Top
    _           -> if x == y then x else Top
  meet x y = case (x, y) of
    (Bottom, _) -> Bottom
    (_, Bottom) -> Bottom
    (Top, x')   -> x'
    (x', Top)   -> x'
    _           -> if x == y then x else Bottom
  leq x y = case (x, y) of
    (Bottom, _) -> True
    (_, Top)    -> True
    _           -> x == y
```
and \({\mathcal{S}}^V\) can be written as a map lattice:
```haskell
let allVars = collectVars program
reify allVars $ \ (Proxy :: Proxy s) -> (bottom :: MapLattice s Text Sign)
```

Note that \(\sqsubseteq\) is derived automatically from the rules of the map lattice.

Similarly, \(\mathcal{S}^{V^{P}}\) is also a map lattice, but we don't need that result.

We can use *Hasse diagrams* to represent lattices. The nodes in a Hasse diagram are elements in the lattice, and there is an edge between \(x_1,x_2\) iff \(x_1\sqsubseteq x_2\) and there is no element \(y\) such that \(x_1\sqsubseteq y\) and \(y\sqsubseteq x_2\). For example, the `Sign` lattice can be drawn as:
{% graphviz %}
digraph sign_lattice {
    rankdir = BT;
    node [shape = plaintext];
    edge [arrowhead = none];
    "⊥" -> {"+", "-", "0"};
    {"+", "-", "0"} -> "⊤";
}
{% endgraphviz %}

The *height* of a lattice is the length of the longest path from \(\top\) to \(\perp\) in the Hasse diagram. The `Sign` lattice has height 2.

Later we will use concepts like "complete lattice with finite height". Note that infinite lattices can also be complete lattice with finite height. Consider the lattice \(\mathbb{N}\cup\{\top,\perp\}\) with the following lattice:
{% graphviz %}
digraph sign_lattice {
    rankdir = BT;
    node [shape = plaintext];
    edge [arrowhead = none];
    "⊥" -> {"0", "1", "2", "..."};
    {"0", "1", "2", "..."} -> "⊤";
}
{% endgraphviz %}

It's an infinite lattice, but it's a complete one (i.e. every element have joins and meets) and its height is 2.

## Constraint Equations

To make sure that the sign analysis result is correct, we introduce some constraints that every correct result should have. In later posts we'll prove that these constraints are sufficient for a sound solution.

If we view functions in \(\mathcal{S}^{V}\) as abstract states of a program, then given a statement \(s\), we can write down the difference between the value of \(f:P\to V\to\mathcal{S}\) on the beginning and the end of \(s\) (which is called *transfer function* in static analysis):
\[\mathrm{transfer}(s)(f(\mathrm{begin}(s))):=f(\mathrm{end}(s)).\]

Here's the explicit definition of the transfer function:
```haskell
transferFn :: CfgNode -> MapLattice s Text Sign -> MapLattice s Text Sign
transferFn node (MapLattice state) = case cfgNodeStmt node of
  -- Assignment statement iterates over the expression to decide the value
  T.Assign var expr -> MapLattice (M.insert var (evalSign state expr) state)
  -- We don't know what user will input, so an input statement will
  -- give the variable `Top` to the variable
  T.Input var       -> MapLattice (M.insert var Top state)
  -- Other statements doesn't change the state
  _                 -> MapLattice state

evalSign :: M.Map Text Sign -> T.Expr -> Sign
evalSign state expr = case expr of
  T.Int n
    | n < 0     -> Neg
    | n == 0    -> Zero
    | otherwise -> Pos
  -- assignments like `x = x + 1` requires looking up old values
  T.Var v     -> Data.Maybe.fromMaybe Bottom (M.lookup v state)
  T.BinOp op e1 e2 -> evalBinOp op (evalSign state e1) (evalSign state e2)
  T.UnOp op e  -> evalUnOp op (evalSign state e)
```

Where the `T.BinOp` and `T.UnOp` branches in `evalSign` are just tedious rules:
```haskell
evalBinOp :: T.Op -> Sign -> Sign -> Sign
evalBinOp T.Add = \s1 s2 -> case (s1, s2) of
  (Bottom, _) -> Bottom
  (_, Bottom) -> Bottom
  (Zero, s)   -> s      -- Zero plus any number returns itself
  (s, Zero)   -> s
  (Pos, Pos)  -> Pos
  (Neg, Neg)  -> Neg
  _           -> Top
evalBinOp T.Div = \s1 s2 -> case (s1, s2) of
  (Bottom, _) -> Bottom
  (_, Bottom) -> Bottom
  (_, Zero)   -> Bottom -- Divided by zero gives invalid sign
  (Zero, _)   -> Zero
  (Pos, Pos)  -> Top -- In integer arithmetic, 1/2=0, 4/2=2, so the sign is unknown
  (Neg, Neg)  -> Top -- The same as above
  _           -> Top
-- ...
```

We can also get some constraints from the control flow of the program. Let \(s_1,s_2,\dots,s_n\) be the predecessor of statement \(s\) in the CFG, then
\[f(\mathrm{begin}(s))=\bigsqcup_{i=1}^nf(\mathrm{end}(s_i)).\]

Putting these two things together, we have a set of equations that every correct result should have:
\[f(\mathrm{end}(s))=\mathrm{transfer}(s)\left(\bigsqcup_{s'\in\mathrm{pred}(s)}f(\mathrm{end}(s'))\right),\ \forall s\in S\tag{1}\]
where \(\mathrm{pred}(s)\) is the predecessor of \(s\). These constraints applies to every sound solution \(f\), so it will definitely applies to the vector \(\Sigma=(\sigma_1,\sigma_2,\dots,\sigma_{|S|})\) we want to solve:
\[\sigma_i=\mathrm{transfer}(s_i)\left(\bigsqcup_{j\in\{k|s_k\in\mathrm{pred}(s_i)\}}\sigma_j\right),\ i=1,2,\dots,|S|.\]

By finding the least solution of the following equations, we can get \(\Sigma\) and solve the sign analysis problem:
\[x_i=\mathrm{transfer}(s_i)\left(\bigsqcup_{j\in\{k|s_k\in\mathrm{pred}(s_i)\}}x_j\right),\ i=1,2,\dots,|S|.\tag{2}\]

If we want to analyze the program in the point \(\mathrm{begin}(s')\), we can write down the relation in terms of \(\mathrm{begin}(s)\) and solve the equations:
\[x_i=\bigsqcup_{j\in\{k|s_k\in\mathrm{pred}(s_i)\}}\mathrm{transfer}(s_j)(x_j),\ i=1,2,\dots,|S|\]

There is one difference though: if \(s\) is the first statement of the program, then \(\mathrm{begin}(s)\) may contain information different than other points. In sign analysis, there is no difference.

## Fixed Points and Monotone Functions

Let \(X=(x_1,\dots,x_{|S|})\), then the equation (2) becomes \(X=F(X)\) for some complex (but known) function \(F\). So the problem is reduced to finding the least fixed point of a function \(F\).

We can prove that the function \(F\) (and most such functions in DFA) are *monotone*, and in next section we will prove that the least fixed point of \(F\) always exists and the algorithm to calculate it is almost trivial.

Let \(X,Y\) be lattices. A function \(f:X\to Y\) is *monotone* iff for every \(x_1,x_2\in X\), if \(x_1\sqsubseteq x_2\), then \(F(x_1)\sqsubseteq F(x_2)\).

The following is the proof that \(F\) is monotone (the proof is not required for the story. Feel free to skip the proofs).

*proof*. First, we decompose \(F\) into two functions: \(F=T\circ JOIN\) where
\[T(x_1,\dots,x_{|S|})=(\mathrm{transfer}(s_1)(x_1),\dots,\mathrm{transfer}(s_{|S|})(x_s)),\]
\[JOIN(x_1,\dots,x_{|S|})=\left(\bigsqcup_{j\in\{k|s_k\in\mathrm{pred}(s_1)\}}x_j,\dots,\bigsqcup_{j\in\{k|s_k\in\mathrm{pred}(s_{|S|})\}}x_j\right).\]

By proving that \(T\) and \(JOIN\) are monotone and using Lemma 1 (in the appendix), we know that \(F\) is monotone.

By Lemma 2,3 and 4, \(JOIN\) is monotone.

By Lemma 2 and 3, to prove that \(T\) is monotone, we can prove that \(\mathrm{transfer}(s)\) is monotone for every statement \(s\).

The definition of \(\mathrm{transfer}(s)\) is given as `transferFn`. For a specific statement, it's either a function that does nothing or a function \({\mathcal{S}}^V\to(V\to \mathcal{S})\) that fits into Lemma 5:
- The \(f\) is the identity function.
- When the statement is `T.Input`, \(g(x)=\top\).
- When the statement is `T.Assign`, \(g(x)\) is `\x -> evalSign x expr`.

So we need to prove that `\x -> evalSign x expr` is monotone *for every* `expr`. This can be done by structural induction over `evalSign`.
```haskell
evalSign :: M.Map Text Sign -> T.Expr -> Sign
evalSign state expr = case expr of
  T.Int n
    | n < 0     -> Neg
    | n == 0    -> Zero
    | otherwise -> Pos
  T.Var v     -> Data.Maybe.fromMaybe Bottom (M.lookup v state)
  T.BinOp op e1 e2 -> evalBinOp op (evalSign state e1) (evalSign state e2)
  T.UnOp op e  -> evalUnOp op (evalSign state e)
```
- If `expr` is `T.Int`, then it's mapping everything to a constant and is trivially monotone.
- If `expr` is `T.Var`, then it's accessing a value in the input map. It is monotone by the definition of map lattice.
- If `expr` is `T.Binop op e1 e2` and assume that `\x -> evalSign x e1` and `\x -> evalSign x e2` are monotone. By viewing `evalBinOp op` as a function that inputs a product lattice and outputs a lattice and using Lemma 1 and 2, we know that if `evalBinOp op` is monotone, then the composite function is also monotone.
- `T.UnOp` is similar to `T.Binop` except that we only need to use Lemma 1 to compose the two functions.

`evalBinOp op` and `evalUnOp op` are just lookup tables. We can write a simple function to verify their monotonicity by brute force:
```haskell
checkMonotone2 :: Lattice a => (a -> a -> a) -> Bool
checkMonotone2 f =
  let elemList = S.toList elements
  in and [f x1 x2 `leq` f y1 y2 |
            x1 <- elemList,
            x2 <- elemList,
            y1 <- elemList,
            x1 `leq` y1,
            y2 <- elemList,
            x2 `leq` y2]

checkMonotone1 :: Lattice a => (a -> a) -> Bool
checkMonotone1 f =
  let elemList = S.toList elements
  in and [f x `leq` f y | x <- elemList, y <- elemList, x `leq` y]

verifyMonotonicity :: IO ()
verifyMonotonicity = do
  putStrLn "--- Binary ops ---"
  let ops = [(T.Add, "Add"), (T.Sub, "Sub"), (T.Mul, "Mul"), (T.Div, "Div"),
             (T.Mod, "Mod"), (T.Gt, "Gt"), (T.Lt, "Lt"), (T.Eq, "Eq"),
             (T.And, "And"), (T.Or, "Or")]
  mapM_ (\ (op, name) ->
    putStrLn $ name ++ ": " ++ if checkMonotone2 (evalBinOp op) then "OK" else "FAIL"
    ) ops
  putStrLn "--- Unary ops ---"
  let uops = [(T.Not, "Not"), (T.Neg, "Neg")]
  mapM_ (\ (op, name) ->
    putStrLn $ name ++ ": " ++ if checkMonotone1 (evalUnOp op) then "OK" else "FAIL"
    ) uops
```

Run the program via `cabal run stapl-sign -- --check`, and there is `OK` in every operator, so it's indeed monotone. \(\Box\)

## Fixed Point Theorem and Algorithm

Here's the theorem:

**Theorem.** Let \(L\) be a complete lattice with finite height \(h\) and \(f:L\to L\) be a monotone function, then \(f\) has a unique least fixed point.

*proof.* We claim that (a) there exists some \(n\in\mathbb{N}\) such that \(f^n(\perp)\) is a fixed point of \(f\), i.e. \(f^{n+1}(\perp)=f^n(\perp)\), (b) \(f^n(\perp)\) is the unique least fixed point of \(f\).

(a) Assume (on the contrary) that the claim is false, which means for every \(n\in\mathbb{N}\), \(f^{n+1}(\perp)\neq f^n(\perp)\).

By definition of \(\perp\), \(\perp\sqsubseteq f(\perp)\). By assumption, \(\perp=f^0(\perp)\neq f(\perp)\).

Because \(f\) is monotone and \(\perp\sqsubseteq f(\perp)\), therefore \(f(\perp)\sqsubseteq f^2(\perp)\). By assumption, \(f(\perp)\neq f^2(\perp)\). By Lemma 6, \(\perp\neq f^2(\perp)\). Therefore \(\perp,f(\perp),f^2(\perp)\) are different elements.

We can apply \(f\) to \(f(\perp)\sqsubseteq f^2(\perp)\) again and get the conclusion that \(f^2(\perp)\sqsubseteq f^3(\perp)\) and \(\perp,f(\perp),f^2(\perp),f^3(\perp)\) are different elements.

Doing so repeatedly, and we will have a path with more than \(h\) element in the Hasse diagram:
\[\perp\sqsubseteq f(\perp)\sqsubseteq f^2(\perp)\sqsubseteq \dots\sqsubseteq f^h(\perp).\tag{3}\]

Which is a contradiction since the height of the lattice is \(h\).

(b) Let \(x\) be a fixed point of \(f\), then \(x=f(x)\).

By definition of \(\perp\), \(\perp\sqsubseteq x\). Because \(f\) is monotone, therefore \(f(\perp)\sqsubseteq f(x)=x\).

Apply \(f\) again and we have \(f^2(\perp)\sqsubseteq f(x)=x\). Doing so repeatedly, and we can get \(f^n(\perp)\sqsubseteq f(x)=x\). So \(f^n(\perp)\) is the least fixed point.

The uniqueness is the direct result of anti-symmetry: if \(x\) is another least fixed point, then \(x\sqsubseteq f^n(\perp)\). We also have \(f^n(\perp)\sqsubseteq x\) from the discussion above, so \(x=f^n(\perp)\). \(\Box\)

The proof is constructive: from the proof, we can get a simple algorithm that calculates the fixed point of any function \(f\) (which is called *naive fixed point algorithm* in SPA textbook): just calculate \(f^n(\perp)\) until it converges.

We can gain some intuition (not a rigorous proof!) about the algorithm when we generalize it a bit. Suppose we want to find the least fixed point of \(f(x)=e^x-1.5\) on the lattice \([-3,3]\subseteq\mathbb{R}\). It's the left-most intersection between \(y=x\) and \(y=e^x-1.5\): [^geogebra]
![1](/myblog/assets/2026-07-19/init.png)

[^geogebra]: These plots are drawn using [GeoGebra](https://www.geogebra.org/classic).

Let's start from \(\perp=-3\) and draw the line \(x=-3\). Its intersection with \(e^x-1.5\) is the value of \(f(\perp)\approx 1.45\):
![2](/myblog/assets/2026-07-19/first.png)

Draw two lines perpendicular to Y axis and X axis respectively, then we got \(f(f(\perp))\approx 1.27\):
![3](/myblog/assets/2026-07-19/second.png)

We can continue the process until it converge to the fixed point:
![4](/myblog/assets/2026-07-19/end.png)

You can see in the plot that the relations in equation (3) also holds.

The following is StaPL's fixed point algorithm. It's more general in that it calculates both \(\mathrm{begin}(s)\) and \(\mathrm{end}(s)\), considers the entry point and uses `combine` rather than join to collect information from its predecessors:
```haskell
forwardAnalysisNaive :: Lattice a => (a -> a -> a) -> Cfg -> a -> (CfgNode -> a -> a) -> AnalysisResult a
forwardAnalysisNaive combine cfg entryFact transferFn = loop ins0 outs0
  where
    entryIdx = cfgEntry cfg

    initMap  = bottom <$ cfgNodes cfg
    ins0     = M.insert entryIdx entryFact initMap
    outs0    = M.insert entryIdx (transferFn (nodeAt entryIdx) entryFact) initMap

    preds n = M.findWithDefault [] n (cfgPred cfg)
    nodeAt n = cfgNodes cfg M.! n

    loop ins outs =
      -- For every node...
      let (ins', outs') = foldl' processNode (ins, outs) $ M.keys (cfgNodes cfg)
          -- ...calculate the function
          processNode (insAcc, outsAcc) idx =
            let newIn = foldl combine bottom [outsAcc M.! p | p <- preds idx]
                newOut = transferFn (nodeAt idx) newIn
                 in (M.insert idx newIn insAcc, M.insert idx newOut outsAcc)
      -- If `F(X)=X`, then return, otherwise continue
      in if outs' == outs
         then AnalysisResult ins' outs'
         else loop ins' outs'
```

There are many algorithms that are more efficient than the naive fixed-point algorithm, but they are not very interesting and there are already too much content in this post.

## Appendix: Lemmas

Most lemmas are exercises in the SPA textbook. I'll generalize the lemma only when it doesn't increase the complexity in proofs or notations.

**Lemma 1.** Let \(X,Y,Z\) be lattice, \(f:X\to Y,g:Y\to Z\) be monotone function, then \(g\circ f:X\to Z\) is also monotone.

*proof.* For every \(x_1,x_2\in X\), if \(x_1\sqsubseteq x_2\), then \(f(x_1)\sqsubseteq f(x_2)\), then
\[(g\circ f)(x_1)=g(f(x_1))\sqsubseteq g(f(x_2))=(g\circ f)(x_2).\]

Therefore \(g\circ f:X\to Z\) is monotone. \(\Box\)

**Lemma 2.** Let \(X,Y\) be a lattice, \(f:X\to Y^n\) and \(f_i\) be its component on each dimension, i.e. \(f(x)=(f_1(x),\dots,f_n(x))\), then every \(f_i\) is monotone iff \(f\) is monotone.

*proof.* Let \(x,x'\in X\). If \(x\sqsubseteq x'\), then by definition of product lattice,
\[\forall i,f_i(x)\sqsubseteq f_i(x')\Leftrightarrow (f_1(x),\dots,f_n(x))\sqsubseteq (f_1(x'),\dots,f_n(x')).\ \Box\]

**Lemma 3.** Let \(X,Y,Z\) be lattices. For \(f:X\to Z\), we can construct a function \(f':X\times Y\to Z\) using \(f'(x,y)=f(x)\). If \(f\) is monotone, then \(f'\) is also monotone.

*proof.* For every \((x,y)\sqsubseteq(x',y')\), we have \(x\sqsubseteq x'\), therefore \(f'(x,y)=f(x)\sqsubseteq f(x')=f'(x',y')\). \(\Box\)

**Lemma 4.** Let \(X\) be lattice and \(x_1,x_2\in X\). If we view \(x_1\sqcup x_2\) as functions \(X^2\to X\), then \(\sqcup\) are monotone (similarly, \(\sqcap\) is monotone. I'll leave it as an exercise).

*proof.* For every \((x_1,x_2)\sqsubseteq(x'_1,x'_2)\), we need to prove that \(x_1\sqcup x_2\sqsubseteq x'_1\sqcup x'_2\).

Because \((x_1,x_2)\sqsubseteq(x'_1,x'_2)\), therefore \(x_1 \sqsubseteq x'_1,x_2\sqsubseteq x'_2\).

By (the first part of) definition of \(\sqcup\) (applied on \(x'_1\sqcup x'_2\)), \(x_1' \sqsubseteq x'_1\sqcup x'_2,x_2' \sqsubseteq x'_1\sqcup x'_2\). Therefore \(x_1\sqsubseteq x'_1\sqcup x'_2,x_2\sqsubseteq x'_1\sqcup x'_2\).

By (the second part of) definition of \(\sqcup\) (applied on \(x_1\sqcup x_2\)), \(x_1\sqcup x_2\sqsubseteq x'_1\sqcup x'_2\). \(\Box\)

**Lemma 5.** Let \(X,Y\) be lattices, \(f: X\to(A\to Y)\) and \(g: X\to Y\) are monotone functions. Given an \(a_0\in A\), the function \(h(x)=f(x)[a_0\mapsto g(x)]\) is monotone.

*proof.* For every \(x_1,x_2\in X\) where \(x_1\sqsubseteq x_2\), we need to prove that \(f(x_1)[a_0\mapsto g(x_1)]\sqsubseteq f(x_2)[a_0\mapsto g(x_2)]\).

\(f(x_1)[a\mapsto g(x_1)]\) and \(f(x_2)[a\mapsto g(x_2)]\) are map lattice \(A\to Y\). To prove \(f(x_1)[a_0\mapsto g(x_1)]\sqsubseteq f(x_2)[a_0\mapsto g(x_2)]\), we need to prove that for every \(a\in A\), the value of \(f(x_1)[a_0\mapsto g(x_1)]\) on \(a\) is less than the value of \(f(x_2)[a_0\mapsto g(x_2)]\) on \(a\):
- If \(a=a_0\), then the value is \(g(x_1),g(x_2)\) respectively. The proposition holds because \(g\) is monotone.
- If \(a\neq a_0\), then the value are the same as \(f(x_1)\)'s value and \(f(x_2)\)'s value on \(a\). 
  
  Because \(f\) is monotone, \(f(x_1)\sqsubseteq f(x_2)\). By definition of map lattice, for every \(a\in A\), the value of \(f(x_1)\) on \(a\) is less than the value of \(f(x_2)\) on \(a\). Thus the propersition holds. \(\Box\)

**Lemma 6.** Let \(X\) be a partial order and \(x_1,x_2,x_3\in X\). If \(x_1\sqsubseteq x_2\), \(x_2\sqsubseteq x_3\) and \(x_2\neq x_3\), then \(x_1\neq x_3\).

*proof.* Assume that \(x_1=x_3\), then by symmetry, \(x_3\sqsubseteq x_1\).

Because \(x_1\sqsubseteq x_2\), therefore by transitivity, \(x_3\sqsubseteq x_2\).

Because \(x_2\sqsubseteq x_3\), by anti-symmetry, \(x_2=x_3\) (contradicts to \(x_2\neq x_3\)). Therefore the assumption is false. \(\Box\)

****
