#import "/preamble.typ":*
#import "./../category-theory-notations.typ":*
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#show: thmrules

Let $X, Y$ be topological spaces, and let $f : X -> Y$.
Let $C_X (-;bb(R))$ be the sheaf of continuous real-valued functions $X -> bb(R)$,
similarly $C_Y$.

#theorem[$f$ induces a natural transformation of functors $f^sharp
: C_Y (-; bb(R)) => f_ast C_X (-; bb(R))$. Moreover, for each open
subset $U$ of $Y$, the induced map $C_Y (U; bb(R))->C_X (f^(-1)(U);
bb(R))$ is a $bb(R)$-algebra homomorphism.]

Let $f : M -> N$ be a continuous map between smooth manifolds.
*Notation:* Let $cal(O)_M, cal(O)_N$ be the sheaves of smooth functions on $M,N$
respectively.

Important observation:
#theorem[
    If $f : M -> N$ is smooth, then $f^sharp$ restricts to a natural transformation of
    $bb(R)$-algebras $cal(O)_N => f_ast cal(O)_M$.
   
    Conversely, if $f : M -> N$ is continuous, and $f^sharp : C_N -> f_ast C_M$ restricts to
    a natural transformation of sheaves of $bb(R)$-algebras $cal(O)_N => f_ast cal(O)_M$,
    then $f$ is smooth.
]
#proof[
    The forward direction is easy as the composition of smooth functions is smooth.

    For the converse direction, note that if $U$ is a local coordinate
    chart on $N$, so there is a diffeomorphism $phi : bb(R)^n -> N$,
    then $f :f^(-1) (U) -> U$ is smooth iff $phi^(-1) circle.small f :
    f^(-1)(U) -> bb(R)^n$ is smooth, and this is smooth iff each
    component $f_i = pi_i circle.small phi^(-1) circle.small f$ is smooth, $1<=i<=n$.
    But $f_i$ is just $f^sharp_U (pi_i circle.small phi^(-1))$, so if $f^sharp$
    carries smooth functions to smooth functions, then $f_i$ is smooth for each $i$.
]

Big takeaway:
*Sheaves can be used to accomplish the same functionality as charts, i.e., detecting whether a map is smooth.* We can also use them to *define* a manifold, instead of using charts to define a manifold. We'll return to this later.

*Notation.* If $X$ is a topological space, let $tau(X)$ denote its topology,
regarded as a poset category. So, a sheaf on $X$ is a kind of functor $[op(tau(X));Set]$
If $x$ is an element of $X$, let $tau(X)_x$ be the sub-poset of the topology containing
all open sets that contain $x$.

#definition[Stalk of a presheaf at a point][
    If $P$ is a presheaf on $X$, then the *stalk of $P$ at x* is defined
    to be the colimit of $P$ when restricted to $op(tau(X)_x)$
]

*Notation.* $P_x$ is the stalk of $P$ at $x$.

In the context of sheaf theory there is an important convention to be aware of.
If $X$ is a topological space, and $P: op(tau(X)) -> cal(A)$
is some presheaf value in $A$, it is convenient to assume that $P$
sends the empty set $emptyset$ to the terminal object $1$ in $cal(A)$.
We can think of this as "ignoring" the empty set as a special "edge case"
we don't want to consider, so we just send it to 1 "by default."

#theorem[Stalk is adjoint to direct image][
    Let $x$ be a point in the space $X$. Regard $x$ as a continuous function
    $x : 1 -> X$. A presheaf on $1$ is just a set. Describe the direct image functor
    $x_ast : Set -> Psh(X)$. Prove that the stalk functor $x^ast : Psh(X) -> Set$
    is (left? right?) adjoint to the direct image functor $x_ast$.
]

Later we will see that something similar holds for any continuous map $f : Y->X$,
not just singleton inclusions $x : 1 ->X$.

#theorem[
    Let $P$ be a presheaf on $X$. The stalk of $P$ at $x$ can be characterized as follows:
    it is the set $product.co_(U in tau(X)_x ) P(U) \/ ~$, where $(U, f) ~ (V, g)$ iff
    there exists an open set $W$ containing $x$, such that $W subset U inter V$,
    and $P(iota_(W,U) )(f) = P(iota_(W, V) )(g)$.
]
#proof[
    Exercise.
    One must take the usual equivalence relation appearing in the definition of a colimit
    and prove that it is equivalent to $~$. The main part of this exercise
    is proving that $~$ is already an equivalence relation as defined here.
]

Observe that taking colimits is functorial - if there is a natural transformation $F => G$,
it induces a natural transformation $colim(F) => colim(G)$. Taking stalks
is therefore functorial: a natural transformation $alpha : P => Q$ induces
a morphism of stalks $P_x -> Q_x$.

#theorem[Characterization of the stalk of $C_X (-; bb(R))$][
    Let $X$ be a topological space. Then $C_X (-; bb(R))$ is a sheaf of
    $bb(R)$-algebras. If $x in X$, then the stalk $C_X (- ; bb(R))_x$ is also
    an $bb(R)$ algebra.

    Using the universal property of the colimit, there is a map
    $C(- ; bb(R))_x -> bb(R)$ given by "evaluate $(U,f)$ at $x$".

    The kernel of this map is a maximal ideal; it is the
    *single unique maximal ideal* of $C(-; bb(R))_x$,
    and the quotient field after modding out by this ideal is isomorphic to $bb(R)$.    

    If $M$ is a smooth manifold, and $x$ is a point in $X$,
    the same holds for $cal(O)_(M,x)$:
    the map $cal(O)_(M, x)-> bb(R)$ has for its kernel 
    the single unique maximal ideal of the ring,
    containing all those pairs $(U, f)$ where $f(x)=0$,
    and the quotient field is isomorphic to $bb(R)$.
]
#proof[Exercise]
In honor of this theorem, rings with a single unique maximal ideal are called *local rings*.


#theorem[
    Let $f : M -> N$ be any continuous map between smooth manifolds, and let
    $alpha : cal(O)_N -> f_ast cal(O)_M$ be *any natural transformation* between
    sheaves of $bb(R)$-algebras, where each $alpha_U$ is a $bb(R)$-algebra homomorphism.

    Then $alpha = f^sharp$. In particular, the assumption that $tau$
    *exists at all* implies that $f^sharp$ is a well-defined natural
    transformation $cal(O)_N -> f_ast cal(O)_M$, i.e., sends smooth
    functions to smooth functions, so $f$ is smooth.
]
#proof[
    Fix $U$ an open subset of $N$ and $g$ an element of $cal(O)_N$.
    We want to prove $alpha(g) = g circle.small f$. It suffices to prove that
    they agree at every point, because they are functions. So, it suffices to prove
    $alpha(g)(x) = (g circle.small f)(x)$ for all $x$ in $U$.
    By the above theorems about local rings, it suffices to prove that
    the elements of the stalk $[alpha(g)], [ g circle.small f]$ in $cal(O)_(M,x)$
    are in the same coset of the unique maximal ideal, because the cosets
    of the unique maximal ideal are the sets of functions which have the same value at $x$.

    Therefore, how does $alpha$ act on stalks? It must induce an
    $bb(R)$-algebra homomorphism $cal(O)_(N,f(x)) -> cal(O)_(M,x)$.
    This will induce an $bb(R)$-algebra homomorphism between the quotient
    $bb(R)$-algebras, $bb(R) -> bb(R)$, once one divides out by the
    maximal ideal; such a homomorphism is obviously the identity.

    Suppose $g(f(x)) = r$ some real number. Then $g$ and the constant
    function at $r$ lie in the same coset in $cal(O)_(N,f(x))$.
    The action of $alpha$ on stalks preserves these cosets, so
    $(alpha(g))_x$ is in the same coset as $alpha(r)_x$.
    Because $alpha$ is assumed to be a $bb(R)$-algebra homomorphism,
    it preserves $bb(R)$, so $alpha(r)=r$. Thus, the coset of
    $alpha(g)_x$ in $cal(O)_(M,x)$ is $r$, so the value of $alpha(g)(x)=r= g(f(x))$,
    and we are done.
]

The Grothendieck construction is usually defined as follows: we have
some base category $bb(B)$, a contravariant functor $Psi :
op(bb(B))->Cat$, and we define a category whose objects are pairs $(b,x)$, where $b$ is in $bb(B)$
and a morphism $(b, x)-> (b', x')$ is a pair $(f : b -> b', g : x -> Psi(f)(x'))$.

It is clear that some kind of dualization of this definition can be used to come up with the following:

Let $Psi : Top -> Cat$ be the covariant functor which associates to $X$ the category $Sh(X)$
of sheaves of commutative $bb(R)$-algebras. The *category of $bb(R)$-ringed spaces*
is the category whose objects are pairs $(X, cal(F))$ where $X$ is a space and $cal(F)$
is a sheaf of $bb(R)$-algebras. A morphism of ringed spaces $(X,cal(F))->(Y,cal(G))$ is a pair
$(f : X -> Y, alpha : cal(G) => f_ast cal(F))$.

If $(X, cal(F))$ is an $bb(R)$-ringed space, then for any open subset $U$, $(U, cal(F)|_U )$ is
also an $bb(R)$-ringed space.

Here is an interesting alternative definition of the category of smooth manifolds.

#definition[Manifold][
The *category of manifolds* is a certain (fully faithful) subcategory of the category of $bb(R)$-ringed spaces.

For any $n$, the $bb(R)$-ringed space $(bb(R)^n, cal(O)_(bb(R)^n))$ is a manifold.

If $(X, cal(F))$ is a ringed space, where $X$ is second-countable and Hausdorff,
and $X$ has an open cover ${U_i}$ where each $(U_i, cal(F)|(U_i))$ is isomorphic to
$(bb(R)^n, cal(O)_(bb(R)^n))$ for some $n$, then $(X, cal(F))$ is a smooth manifold.
]

These isomorphisms $(bb(R)^n, cal(O)_(bb(R)^n)) cong (U_i, cal(F)|U_i)$ are much like
*charts*, but we don't include the requirement that the composition of charts $phi^(-1) circle.small psi$ be smooth where it is defined. It is helpful to prove that this follows from
the assumption that $phi, psi$ are both isomorphisms of ringed spaces, so their composition is
also an isomorphism of ringed spaces, where it is defined.

*Takeaway*: One motivation for sheaves is that
every branch of geometry deals with a class of spaces satisfying certain axioms, and
a sheaf of *good functions* on those spaces. (smooth functions, holomorphic functions, polynomial functions). A good morphism between spaces
is a continuous function $f : X-> Y$  such that precomposition with $f$
sends good functions to good functions. This is equivalent to the usual definition
in terms of coordinate charts, because a coordinate chart $(x_1,...x_n) : U ->bb(R)^n$ ($U subset M$)
is a list of $n$ "good" functions $x_i in cal(O)_M (U)$.

Thus, *each branch of geometry* is essentially the study of a certain full subcategory of the category of $k$-ringed spaces (where $k$ is some field - $bb(R)$, $bb(C)$, or an algebraically closed field). Sheaves are thus the basic building blocks of modern geometry. For more on this perspective, see *Manifolds, Sheaves, and Cohomology* by Torsten Wedhorn, or *Algebraic Geometry* by Hartshorne.

= A generalization of the $Lambda_X tack.l Gamma_X$ adjunction to continuous maps $f : X->Y$

Let $f : X -> Y$ be a continuous map between topological spaces.

$f$ induces a functor $S_f : tau(Y) -> Top\/X$, which sends the open set $U$ in $Y$ to
the inclusion map $f^(-1) (U) subset X$. This leads to a nerve-realization situation induced by $S_f$,
which generalizes the adjunction between $Gamma_X$ and $Lambda_X$ we have described elsewhere,
in the case where $f$ is the identity. Our goal here is to investigate this nerve-adjunction situation and understand how it relates to the adjunctions $Lambda_X tack.l Gamma_X$
and $Lambda_Y tack.l Gamma_Y$.

This nerve-realization adjunction is an adjunction between $Top\/X$ and $Psh(Y)$. This is a little peculiar,
because $f$ somehow does not appear except to identify the open subsets of $X$
that we care about.

One important theorem here seems to be:
#theorem[
    The pullback functor $f^ast: Top\/Y -> Top\/X$ preserves colimits.
]
#proof[
    Colimits in $Top\/X$ are computed in the obvious way,
    the same way they are in $Top$. It is easy to see that
    set-theoretically we get the correct answer, so it is
    only a matter of checking that the topologies agree.
]
#corollary[
    Let $cal(G)$ be any presheaf on $Y$.
    Let $iota_Y : tau(Y) -> Top\/Y$ be the functor that sends
    $U$ to the inclusion $U subset Y$;
    and let $S_f : tau(Y) -> Top\/X$ be the functor described earlier.

    Then:
    #align(center, $f^ast Lambda_Y (cal(G)) = WC(cal(G), S_f) $)
]
#proof[
    $Lambda_Y$ is, by definition, a realization functor,
    i.e. $Lambda_Y (cal(G))$ is the weighted colimit
    $WC(cal(G), iota)$. We have said that $f^ast$
    preserves colimits, so $f^ast (Lambda_Y (cal(G))) = WC( cal(G), f^ast circ iota)$.
    But it is easy to see that $f^ast circ iota = S_f$.
]

This helps us to break down the realization functor as the composite of
a simpler realization followed by a pullback.

#lemma[
    The nerve functor $N_(S_f) : Top\/X -> Psh(Y)$ can be
    factored as $f_ast circle.small N_(iota_Y)$, where $f_ast$ is the direct
    image functor $Psh(X) -> Psh(Y)$
]
#proof[
    Easy.
]

// We have already seen that $f$ induces a *direct image functor*
// between categories of presheaves: $f_ast : Psh(X) -> Psh(Y)$, which sends the presheaf $cal(F)$
// on $X$ to the presheaf $U |-> cal(F)(f^(-1)(U))$.

// There is also $f^ast : Top\/Y -> Top\/X$, the evident pullback functor.

#theorem[
    In the following square:
    \
    #diagram(cell-size: 15mm, $
	Psh(X) edge(f_ast, ->) & Psh(Y) edge("d",Lambda_Y,->) \
	Top\/X edge(f^ast, <-) edge("u", Gamma_X, ->) & Top\/Y
   $)
    
    The composite $f_ast circle.small Gamma_X : Top\/X -> Psh(X) -> Psh(Y)$
    is right adjoint to $f^ast circle.small Lambda_Y : Psh(Y) -> Top\/Y -> Top\/X$.
]
#proof[
    // This is an interesting exercise in point-set topology.
    This follows from what we have done. The top left composite is the nerve $N_(S_f)$.
    The bottom right composite is the realization $R_(S_f)$.
]

#let Et(XX) = [Et($XX$)]
#corollary[
    The nerve-realization adjunction $R_(S_f) tack.l N_(S_f)$ between
    $Top\/X$ and $Psh(Y)$
    restricts to a nerve-realization adjunction between
    $Et(X)$ and $Sh(Y)$.
]
#proof[
    Exercise, one should prove that the left adjoint sends any presheaf
    to an etale space and the right adjoint sends any continuous map to a sheaf.
]

= The inverse image functor
#theorem[The direct image functor $f_ast$ has both a left and right adjoint.]
#proof[
    This follows from the general theory of Kan extensions.
    $f_ast$ is a precomposition functor, it sends $cal(F)$ to its
    precomposition with the functor $f^(-1) : tau(Y) -> tau(X)$.
    Since $Set$ is both complete and cocomplete, and the category $tau(Y)$
    is small, it is possible to apply the weighted limit/colimit formula
    for the right/left Kan extension.
]

The left adjoint is called the *inverse image functor* and it plays an important role.
We will not be as interested in the right adjoint in the following.

We will need a concrete description of this left adjoint in the future,
so it is worth working it out. Apply the weighted colimit formula for the left Kan
extension. Observe that because $tau(X)$ is a poset category,
the weighting sets are either empty, or a singleton set,
and so the weighted colimit can be reduced to an ordinary colimit by
discarding all those objects for which the weight is zero. Write down this colimit.

#theorem[
    The following diagram commutes:\
    #diagram(cell-size: 15mm, $
	Psh(X) edge(f^ast, <-) edge("d", Lambda_X, ->) & Psh(Y) edge("d",Lambda_Y,->) \
	Top\/X edge(f^ast, <-) & Top\/Y
   $)
]
#proof[
    $Lambda_X$ is the left adjoint to $Gamma_X$ and $f^ast$ is the left adjoint to $f_ast$,
    so $Lambda_X circle.small f^ast$ is the left adjoint to $f_ast circle.small Gamma_X$.
    But we have already established that $f_ast circle.small Gamma_X$ is $N_(S_f)$,
    and so its left adjoint is the realization, which we have already established is
    equivalent to the bottom /right path.
]
