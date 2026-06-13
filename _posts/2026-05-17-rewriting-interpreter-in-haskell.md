---
layout: post
title:  "Rewriting My Interpreter in Haskell (Part 2)"
---

> This is the second post of a series about implementing and proving a HM type inference system. Here are [the previous](/myblog/2026/05/10/implementing-hm-type-inference-system.html) and [the next](/myblog/2026/05/24/type-safety-proof.html) posts.

As my daily job gets more and more demanding, I won't stretch myself too hard like what I have done in [the previous post](/myblog/2026/05/10/implementing-hm-type-inference-system.html). So this weekend I [rewrote the entire Lam interpreter using Haskell](https://github.com/heanyang1/interpreter/commit/8f4e4716c0dfecf19b091c0d362cb24fcb989db5) ... with an AI agent.

## The Process

I use OpenCode and its free tier models, mostly DeepSeek V4. The prompt is simple:
> Rewrite the interpreter in Haskell. Make sure that every test is rewritten and passed. ghcup is installed on this machine.

The rewriting session lasted for a few hours. The agent get stuck occasionally:
1. It had a hard time writing the parser. This is understandable since there is no reference implementation of the parser.
2. The interpreter went into infinite loop when running tests. The agent solved it in about an hour without intervention.
3. The agent couldn't implement the step-by-step evaluation, and it decided to implement a simplified evaluation process without asking me.

When all tests are passed, I asked the agent to fuzz the new interpreter: write a Python script to generate random Lam expression and check whether the Rust version and the Haskell version produce the same output. It generated and tested 20k random Lam programs on both versions, fixing some bugs along the way. All tests passed, so we are confident that the two versions should have the same behavior.

## The Result

The generated code is beautiful. It doesn't have the messiness feature of AI-generated code. I think the reason is that the Rust interpreter is clean enough, and Haskell is less noisy than C-like languages.

I'll paste a couple of excerpts from the Rust and Haskell versions here. The code snippet are supposed to do the same job so you can compare them.

You have to write bizarre parser DSL in both versions. In my opinion `parsec` is better because it's at least part of the Haskell language and the compile error is more informative than "there is something wrong at line 2145 of the generated Rust code":
{% highlight rust %}
LetRec: Box<Expr> = {
    <e:Let> => e,
    "letrec" <x:Variable> "=" <evar:LetRec> "in" <ebody:LetRec> => {
        let xclone = x.clone();
        let lam = Box::new(Expr::Lam { x: xclone, e: ebody });
        let arg = Box::new(Expr::Fix { x, e: evar });
        Box::new(Expr::App { lam, arg })
    }
};

Let: Box<Expr> = {
    <e:Func> => e,
    "let" <x:Variable> "=" <e_x:Let> "in" <e_in:Let> => Box::new(Expr::Let { x, e_x, e_in }),
};
{% endhighlight rust %}

{% highlight haskell %}
letrecExpr :: P Expr
letrecExpr =
    try (do
        kw "letrec"
        x <- var
        op "="
        e1 <- letrecExpr
        kw "in"
        e2 <- letrecExpr
        return (EApp (ELam x e2) (EFix x e1)))
    <|> letExpr

letExpr :: P Expr
letExpr =
    try (do
        kw "let"
        x <- var
        op "="
        e1 <- letExpr
        kw "in"
        ELet x e1 <$> letExpr)
    <|> funExpr
{% endhighlight haskell %}


The Haskell version uses recursion to iterate over the constraint, a common trick in pure functional programming:
{% highlight rust %}
fn unification(
    constraints: Vec<Constraint>,
) -> Result<(UnionFind<Variable>, HashMap<Variable, Type>), String> {
    let variables: Vec<Variable> = constraints
        .iter()
        .flat_map(|c| vec![&c.type_l, &c.type_r])
        .flat_map(|t| t.get_all_vars())
        .collect();
    let mut uf = UnionFind::new(variables);
    let mut map: HashMap<Variable, Type> = HashMap::new();
    let mut constraints = VecDeque::from(constraints);
    while !constraints.is_empty() {
        let constraint = constraints.pop_front().unwrap();
        match (constraint.type_l, constraint.type_r) {
            (Type::Bool, Type::Bool) | (Type::Num, Type::Num) | (Type::Unit, Type::Unit) => (),
            (Type::Var(l), Type::Var(r)) => {
                let l_root = uf.find(&l)?.clone();
                let r_root = uf.find(&r)?.clone();
                let root = uf.union(&l, &r).unwrap();
                match (map.remove(&l_root), map.remove(&r_root)) {
                    (Some(lval), Some(rval)) => {
                        constraints.push_back(Constraint {
                            type_l: lval.clone(),
                            type_r: rval,
                            expr_l: format!("val({})", l),
                            expr_r: format!("val({})", r),
                        });
                        Some(lval)
                    }
                    (Some(val), None) | (None, Some(val)) => Some(val),
                    (None, None) => None,
                }
                .and_then(|v| map.insert(root.clone(), v));
            }
{% endhighlight rust %}

{% highlight haskell %}
unification' :: UnionFind Variable -> Map Variable Type -> [Constraint]
    -> Either String (UnionFind Variable, Map Variable Type)
unification' uf mp [] = return (uf, mp)
unification' uf mp (c:cs) = case (typeL c, typeR c) of
    (TNum, TNum) -> unification' uf mp cs
    (TBool, TBool) -> unification' uf mp cs
    (TUnit, TUnit) -> unification' uf mp cs
    (TVar l, TVar r) -> do
        let lRootBefore = case find uf l of Right x -> x; Left _ -> l
        let rRootBefore = case find uf r of Right x -> x; Left _ -> r
        let lVal = Map.lookup lRootBefore mp
        let rVal = Map.lookup rRootBefore mp
        (uf', root) <- union uf l r
        case (lVal, rVal) of
            (Nothing, Nothing) -> unification' uf' mp cs
            (Just lv, Nothing) -> do
                let mp' = Map.insert root lv mp
                unification' uf' mp' cs
            (Nothing, Just rv) -> do
                let mp' = Map.insert root rv mp
                unification' uf' mp' cs
            (Just lv, Just rv) ->
                let newC = Constraint lv rv (show lv) (show rv)
                in unification' uf' mp (newC : cs)
{% endhighlight haskell %}

Another example of loop to recursion. I'm glad that my weird logic to reduce nested if-else doesn't get into the Haskell version:
{% highlight rust %}
fn get_type(mut tau: Type, mut uf: UnionFind<Variable>, mut map: HashMap<Variable, Type>) -> Type {
    loop {
        let vars = tau.get_free_vars();
        if vars.is_empty() {
            return tau;
        }
        let x = vars.first().unwrap();
        let r_opt = uf.find(x);
        if let Ok(r) = r_opt
            && x != r
        {
            tau = tau.substitute(x.clone(), Type::Var(r.clone()));
            continue;
        }
        match r_opt.ok().and_then(|r| map.remove(r)) {
            Some(t_x) => tau = tau.substitute(x.clone(), t_x),
            None => tau = tau.add_one_quantifier(x.clone()),
        }
    }
}
{% endhighlight rust %}

{% highlight haskell %}
getType :: Type -> UnionFind Variable -> Map Variable Type -> Type
getType tau uf mp =
    let fvs = getFreeVars tau in
    if null fvs
        then substituteVars tau
        else let x = head fvs in
            case find uf x of
                Left _ -> getType (addOneQuantifier tau x) uf mp
                Right r -> if r /= x
                    then getType (substituteVar x (TVar r) tau) uf mp
                    else case Map.lookup r mp of
                        Just t -> getType (substituteVar x t tau) uf mp
                        Nothing -> getType (addOneQuantifier tau x) uf mp
  where
    substituteVars t = case t of
        TVar v -> maybe t substituteVars (Map.lookup v mp)
        TFn a r -> TFn (substituteVars a) (substituteVars r)
        TProduct l r -> TProduct (substituteVars l) (substituteVars r)
        TSum l r -> TSum (substituteVars l) (substituteVars r)
        TForall a tau' -> TForall a (substituteVars tau')
        _ -> t
{% endhighlight haskell %}

The "pseudo do-notation" implemented using Rust macro looks exactly the same as Haskell's do-notation:
{% highlight rust %}
impl ToGraph for Expr {
    fn to_graph(&self, parent: NodeIndex) -> Writer<()> {
        match self {
            Expr::Var(_)
            | Expr::DeBruijn(_)
            | Expr::Num(_)
            | Expr::True
            | Expr::False
            | Expr::Unit => {
                do_!(new_node(self, parent, "red"), Writer::ret(()))
            }
            Expr::Addop { binop, left, right } => do_!(
                new_node(binop, parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
            Expr::Mulop { binop, left, right } => do_!(
                new_node(binop, parent, "red") => cur,
                left.to_graph(cur.clone()),
                right.to_graph(cur)
            ),
{% endhighlight rust %}

{% highlight haskell %}
instance ToGraph Expr where
    toGraph e parent counter = case e of
        EVar _ -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        EDeBruijn _ -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        ENum _ -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        ETrue -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        EFalse -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next
        EUnit -> do
            (_, next) <- newNode (show e) parent counter "red"
            return next

        EAddop op left right -> do
            (cur, next1) <- newNode (show op) parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2

        EMulop op left right -> do
            (cur, next1) <- newNode (show op) parent counter "red"
            next2 <- toGraph left cur next1
            toGraph right cur next2
{% endhighlight haskell %}

## Conclusion

AI have lowered the barrier to learn and use Haskell. Before the AI agent era, I thought I'll never be able to write anything non-trivial in Haskell because of its weird Monadic syntax and incomprehensible error message. These are no longer the problem now as AI agents can analyze and fix complex compile error for me.

Haskell will probably be my go-to language when the dependencies are simple and the performance doesn't matter, such as writing indie compilers and interpreters.
