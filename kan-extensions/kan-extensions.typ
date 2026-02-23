#import "/preamble.typ":*
#import "./../category-theory-notations.typ":*
#show: thmrules
= Relative left adjoint

#theorem[
  Let $A, B, C$ be categories.
  Let $F : A -> B$.
  Let $G : C -> B$.
  Suppose for each $a$ in $A$
  there is a representing object $c_a$ in $C$
  for the covariant functor $Hom(F(a),G(-)) : C -> Set$.
  Let $eta_a$ be the universal element of the presheaf,
  i.e., $eta_a : F(a) -> G(c)$ is initial
  among maps from $F(a)$ into the image of $G(-)$.
  Then the map $a |-> c_a$ extends
  in a unique way to a
  functor $L : A -> C$,
  such that $eta : F => G L$ is a natural transformation.
]

#proof[Exercise.]

#theorem[
  Let $A, B, C$ be categories.
  Let $F : A -> B$.
  Let $G : C -> B$.
  Let $L : A -> C, eta : F => G L$ be as above.

  Let $S : A ->C$ be an arbitrary functor.
  Let $sigma : F => G S$ be a natural transformation.
  By the universal property of $(L(a), eta_a : F(a) -> G(L(a))$,
  for each $a$ there is a unique $hat(sigma)_a : L(a) -> S(a)$
  such that $G(hat(sigma_a)) circ eta_a = sigma_a$.

  Prove that $hat(sigma) : L => S$ is natural.
]
#proof[Exercise.]

#corollary[Initial factoring property of $L$][
  Let $A, B, C, F, G, L, eta$
  be as above.

  Regard $G$ as defining a functor
  $(G circle.small - ) [A;C] -> [A; B]$ by post-composition.
  Then $(L, eta : F => G circle.small L)$ is a
  universal arrow from $F$ into $(G circle.small -)$.
  We say that $(L, eta)$ is the
  *left Kan lift* of $F$ along $G$.
]
#proof[Straightforward consequence of the theorem]


Let $A, B, C$ be categories, $F :A -> B, G : C -> B$, $L : A -> C$,
$eta : F => G circle.small L$, such that $(L, eta)$ is a left Kan lift
of $F$ along $G$.

Now, introduce a new category $S$, and $J : S -> A$ a functor.
It is *not necessarily the case* that $(L circle.small J, eta J)$
is a left Kan lift of $F circle.small J$ along $G$. We introduce a definition.

#definition[Absolute left Kan lift][
  Let $A, B, C$ be categories and $F : A -> B, G : C ->B$
  be functors. Let $(L : A->C, eta: F => G circle.small L)$
  be the left Kan lift of $F$ along $G$.

  Then $(L, eta)$ is an *absolute left Kan lift* if for all categories $S$
  and all $J : S -> A$, $(L circle.small J, eta J)$ is the left
  Kan lift of $F circle.small J$ along $G$.
]

#theorem[
  Let $A, B, C$ be categories, $F : A -> B, G : C -> B$,
  $L : A -> C$, $eta : F => G circle.small L$.

  Then $(L, eta)$ is an *absolute left Kan lift* of
  $F$ along $G$ iff $(L,eta)$ is a *relative left adjoint*
  to $G$ relative to $F$.
]
#proof[Exercise.]

= Kan extensions
In this section:

Let $M, C, A$ be categories, where $M$ is assumed to be small.
Let $K : M -> C, T : M -> A$. 

Let $(- circle.small K) : [C; A] -> [M; A]$
denote the precomposition functor.

The *left Kan extension* of $T$ along $K$,
if it exists, is a universal arrow from $T$ into $(- circle.small K)$.


#theorem[
Let $N_K : C -> hat(M), N_T : A -> hat(M)$
be the associated nerve functors, so $N_K (c) = Hom(K -, c)$
and $N_T (a) = Hom(T -,a)$.

  Let $S : C->A$.
  
  There is a bijection
  #align(center,$Nat(T, S circle.small K) tilde.equiv Nat(N_K, N_T circle.small S)$)

  This bijection is natural in $S$.
]

#corollary[Existence of Kan extensions][
  Let $(N_T circle.small -) : [C;A] -> [C; hat(M)]$
  denote the postcomposition functor.
  
  There is an *isomorphism* of categories
  #align(center, $T arrow.b (- circle.small K) tilde.equiv N_K arrow.b (N_T circle.small -)$)

  As a consequence, one category has an initial object iff the other does,
  and so there is a universal arrow from $T$ into $(- circle.small K)$
  iff there is a universal arrow from $N_K$ into $(N_T circle.small -)$.

  That is, there is a left Kan extension of $T$ along $K$ iff
  there is a left Kan lift of $N_K$ along $N_T$, and they are equal.
]

#theorem[
  If $A$ is cocomplete, then the left Kan extension of $T$ along $K$ exists and is given by
  the formula

  #align(center,$c |-> WC(T, N_K (c))$)
]
#proof[
  If $A$ is cocomplete then $T$ has all weighted colimits (by means of the category of elements construction)
  so the functor is well-defined.

  Unfolding the definitions $c |-> WC(T, N_K (c))$ is exactly the relative left adjoint
  to $N_T$ relative to $N_K$, these evidently have the same universal property.

  The relative left adjoint of $N_T$ relative to $N_K$ is known to also be
  the left Kan lift of $N_K$ along $N_T$.

  Thus, it is also the left Kan extension of $T$ along $K$.
]

We have seen that left Kan extensions correspond to left Kan lifts.

If $L : C -> A$ is a left Kan extension which is given by the formula above, we say $L$
is *pointwise*.

Observation: If $A$ is cocomplete, and $M$ is small then the nerve functor $N_T$
has a left adjoint, called the *realization* of $T$, $R_T : hat(M) -> A$,
defined as $R_T (P) = WC(T, P)$. In this case, the left Kan extension is just
$L = R_T circle.small N_K$. However, we don't need *all* colimits to exist in $T$
for this, only the ones of the form $N_K (c)$ for $c$ in $C$, so the pointwise
left Kan extension may still exist if the category is not cocomplete, so
long as the requisite colimits exist.


#definition[Pointwise left Kan extension][
  Let $M, C, A$ be categories, $K : M ->C$, $T: M ->A$.

  Suppose $(L, eta : T => K circle.small L)$ is a left Kan extension of $T$ along $K$.
  Let us write $sigma: N_K => N_T circle.small L$ for the corresponding universal arrow
  making $L$ into a left Kan lift of $N_K$ along $N_T$.
  
  We say that $(L, eta)$ is a *pointwise left Kan extension* if $(L, sigma)$ is
  an *absolute left Kan lift* of $N_K$ along $N_T$, equivalently $L$ is the
  *relative left adjoint* to $N_T$ relative to $N_K$.
]

= Examples

#theorem[Universal arrows are left Kan lifts][
Let $G : D -> C$, and $c$ an object in $C$. Regard $c$ as defining a functor $c : 1 -> C$. Then
  the left Kan lift of $c$ along $G$ is exactly a universal arrow from $c$ into $G$.]
#proof[Exercise]

#theorem[Left adjoints are left Kan lifts][
  Let $G : D -> C$. Let $F : C -> D$ be left adjoint to $G$. Then $(F, eta : 1 => G F)$
  is also the left Kan lift of the identity functor $1_C$ along $G$.
]
#proof[Specialization of the relative left adjoint to the case where the inclusion functor is the identity]

#theorem[Colimits are left Kan extensions][
  Let $F : A -> C$. Let $(!) : A -> 1$ be the unique functor to the terminal category.
  Then the left Kan extension of $F$ along $(!)$ is equivalently the colimit of $F$.
]
#proof[Exercise.]

Example:
What happens when $K : M -> C$ is taken to be just $y_C : M -> hat(M)$? (Assume $A$ is cocomplete.)

#theorem[The realization is a left Kan extension][
  Let $F : C -> E$. The realization $R_F : hat(C) -> E$ is equivalently
  the pointwise left Kan extension of $F$ along $y_C : C -> hat(C)$.
]
#proof[Exercise]
#theorem[The nerve is a left Kan extension][
  Let $F : C -> E$. The nerve $N_F : E -> hat(C)$ is equivalently
  the pointwise left Kan extension of $y_C : C -> hat(C)$ along $F$.
]
#proof[Exercise]

= Some comments on colimits, weighted colimits and simplicial sets

Let $P : C -> Set$ be a functor. The colimit of $P$ can be concretely described as
#align(center, $product.co_(c in C) P(c) \/ ~$)
where $ ~$ is the smallest equivalence relation generated by $(c,x) ~ (d, y)$ if there
exists $f : c -> d$ such that $P(f)(x) = y$.

However, $product.co_(c in C) P(c)$ is more than just a set equipped
with an equivalence relation: it is the set of objects of a
*category*, the category $el(P)$ of elements of the presheaf $P$, and
the set of equivalence classes under the relation is equivalently the
set of *connected components* of the category $el(P)$.

This observation is useful because sometimes theorems about the category $el(P)$
(say, every morphism $f$ factors as $m e$, where $m$ and $e$ have some interesting special properties)
can lead us to better understand the combinatorics of the equivalence relation $~$ and
give a simpler necessary and sufficient condition for two elements to be related under $~$.

Something similar can be said for coends. Let $P : op(C) times C -> Set$
be a functor. Then the coend of $P$ can be described concretely as $product.co_(c in C) P(c,c)\/~$
where $~$ is the smallest relation generated by requiring that $(c, x) ~ (d,y)$ whenever
there exists $f : c -> d$ such that $P(op(id(c)),f)(x) = P(op(f), id(d))(y)$ in $P(c,d)$.
This, too, can be described as a category, which we can perhaps call the "dinatural category of elements" of $P$.
The objects of this $el(P)$ are pairs $(c,x)$ with $x in P(c,c)$, and a morphism $(c, x) -> (d,y)$ is
given by an $f : c -> d$ such that $P(op(id(c)),f)(x) = P(op(f),id(d))(y)$. (It is a useful exercise to check that composition of
morphisms is well-defined.)

We know that if $X$ is a simplicial set, the geometric realization of $X$ is equivalently the coend
#align(center, $integral_(n in Delta_(s d)) X_n times Delta^n$)

(why?)

and in this section we will show how we can understand this coend better by working out some combinatorial properties
of what I have called the "dinatural category of elements."

#lemma[
  Let $Delta_d$ be the semi-simplex category of finite ordinals and injective monotonic morphisms.

  Let $n, m, k$ be objects in $Delta_d$, and $f : n -> m, g : k -> m$ a "co-span" diagram.
  There is a span $(ell, f' : ell -> n, g' : ell -> k)$ making the diagram commute.
]
#proof[Exercise]
#lemma[
  Let $Delta_d$ be the semi-simplex category of finite ordinals and injective monotonic morphisms.

  Let $F : Delta_d -> Top$ be the standard inclusion.

  We will forget the topology on the sets $F(n)$ for now in order to
  establish an interesting combinatorial property of the (covariant)
  category of elements $el(F)$.

  If $(n, a), (m, b)$ and $(k, c)$ are objects in $el(F)$,
  there is a span $(ell in Delta_d, x in F(ell), f' : (ell, x) -> (n,a), g' : (ell, x) -> (m,b))$ 
  making the diagram commute.
]
#proof[Exercise]
#corollary[
  Let $F : Delta_d -> Top$. Let $(n,a)$ and $(m, b)$ be objects in the same connected component.
  There exists a span $((ell, x), f : (ell, x) -> (n,a), g : (ell, x) -> (m, b))$.
]
#proof[
  If $(n, a)$ and $(m, b)$ are related, there exists a zigzag of morphisms in $el(F)$ between $(n,a)$
  and $(m,b)$:
  #align(center,$(n,a) -> (n_0, a_0) <- (n_1, a_1) -> (n_2, a_2) <- ... (m,b)$)
  Argue by induction on the length of the zigzag, applying the previous lemma
  to simplify the zigzag.
]
#corollary[
  Let $F : Delta_d -> Top$. The category structure on $el(F)$ gives
  rise to a partial order on its objects.

  Every connected component of $el(F)$ has a *unique* least element under
  this ordering.
]
#proof[
  The existence of a *minimal* element in each equivalence class
  is easy: the partial order is well-founded because $bb(N)$
  is well founded.

  If $(n, a)$ and $(m, b)$ are two minimal elements
  of the equivalence class, then they are related under the relation.
  By the previous corollary, there is a span connecting them.
  Conclude that both legs of this span are the identity.
]

We will call a minimal element in the equivalence relation above an *interior point.*

#lemma[Let $Delta_(s d)$ be the simplex category of finite ordinals and monotonic morphisms.
  This category has injective-surjective factorizations: every morphism $f : n -> k$ can be factored as
  $f = m circle.small e$ where $m$ is an injection and $e$ is a surjection.
]
#proof[Easy exercise]
#lemma[
  Let $X$ be a simplicial set, and let $el(X)$ be the (contravariant)
  category of elements of $X$. Let $f : (n, x) -> (n', x')$ be a morphism in $el(X)$.
  The injective-surjective factoring of the previous lemma lifts to a factoring of $X$,
  i.e., there is an object $(h,s)$ and a factoring $f : m circle.small e$ such that
  $e : (n,x) -> (h,s)$ is a surjection $n -> h$ and $m : (h,s) -> (n', x')$ is an injection $h->n'$.
]
#proof[Easy exercise]

#lemma[Let $X$ be a simplicial set, and let $el(X)$ be the (contravariant)
  category of elements of $X$. Let $(n, x)$, $(m, y)$, $(m', y')$
  be objects in $el(X)$, and $f : (n, x) -> (m,y), g : (n,x) -> (m', y')$
  be a span, where both $f, g$ are assumed to be surjective.

  Then there is a pair $(h, s)$ and morphisms $f' : (m,y) -> (h,s), g': (m', y') -> (h,s)$
  making the square commute.
]
#proof[
  We argue by well-founded induction on $m$ and $m'$.

  Let $R subset m times m'$ refer to the binary relation: $R(a,b) := exists z in n, f(z)=a and g(z)=b$.

  First, consider the case where $R$ is not injective, i.e., there are distinct elements  $a, a' in m$ such that $R(a,b)$ and $R(a',b)$ for some $b$.
  Then, using the monotonicity of $f,g$, there exists $a in m$ such that $R(a,b)$ and $R(a+1,b)$.
  In this case, let $t : (m, y) -> (n, x)$ be a section of $f : (n, x) -> (m, y)$ such that
  $g(t(a)) = g(t(a+1))$. (Exercise: Why must such a section $t$ exist? Why is $t$ a morphism in $el(X)$?
  Since $g circle.small t$ is not injective, the injective-surjective factorization of $g circle.small t$
  yields a situation $g circle.small t = r circle.small a : (m, y) -> (h_0, s_0) -> (m', y')$, where $a$
  is surjective and not injective, and $h_0 < m$.

  It suffices now to prove the theorem for the span $(a circle.small f :(n,x) ->(h_0, s_0) , g : (n, x) -> (m', y'))$,
  because when we find such a span $(k_1, k_2)$ making the diagram commute, then $(k_1 circle.small a, k_2)$ will be a solution to the original
  problem. Therefore, we apply our induction hypothesis and thus reduce the case $(m, m')$ to $(h_0, m')$, where $h_0 < m$.

  If $R^(-1)$ is not injective, then the same argument applies by symmetry, and we can reduce from $(m,m')$ to $(m, h_1)$ where $h_1 < m'$,
  by induction.

  We can repeat this until we reach the base case of the induction, where $R$ and $R^(-1)$ are both injective.
  In this case, $R$ is a bijection, so $m = m'$, and $f = g$ as morphisms in $Delta_(s, d)$.
  It then follows that $y = y'$ in $X(m)$. (Why? Hint: Choose a section $t$ of $f$.)

  This concludes the proof.
]

#corollary[
  Let $X : op(Delta_(s d)) -> Set$ be a simplicial set; and forget the face maps, so that
  we regard $X$ as a functor $op(Delta_s) -> Set$. Then the objects of $el(X)$
  can be equipped with a partial order, where $(n, x) <= (m, y)$ if there is a morphism
  $f : (m, y) -> (n,x)$ in $el(X)$ (it is convenient to work in the opposite poset,
  so that the ordering agrees with the ordering of $bb(N)$).

  Every connected component contains a unique least element with respect to this ordering.
]
#proof[
  The proof is similar to that of $F : Delta_d -> Set$.
]

#theorem[
  Let $X$ be a simplicial set, and let $P : op(Delta_(s d)) times Delta_(s d) -> Set$
  be the functor $P(n, m) = X_n times F(n)$, where $F : Delta_(s d) -> Top -> Set$
  is the usual inclusion of $Delta_(s d)$ into $Top$, but with the spaces stripped of their topologies.

  The geometric realization of $X$ has, as its underlying set of
  points, the coend $integral_(n in Delta_(s d)) P(n, n)$.

  Let $el(P)$ be the "dinatural category of elements" of $P$, that we
  have defined above; the objects of $el(P)$ are triples $(n, x, a)$,
  where $n$ is a natural number, $x in X_n$, and $a$ is a formal
  convex linear combination on $n$ points; a morphism $f : (n, x, a)
  -> (m, y, b)$ is $f : n -> m$ such that $X(f)(y) = x$ and $F(f)(a) =
  b$.

  The objects of $el(P)$ can be equipped with two distinct partial orderings:
  - $(n,x,a) <=_d (m, y, b)$ if there is an injective monotonic morphism $f : n -> m$ in $Delta_(s d)$ such that
    $X(f)(y)=x$ and $F(f)(a)=b$
  - $(n,x,a) <=_s (m, y, b)$ if there is a surjective monotonic morphism $f : m -> n$ such that
    $X(f)(x) = y$ and $F(f)(b)=a$

  Write $<=_(s d)$ for the smallest partial order containing both of these.
  (Convince yourself that $<=_(s d)$ is antisymmetric.)
  If $(n, x, a)$ and $(m, y, b)$ are objects in the same connected component of $el(P)$,
  connected by a zigzag of morphisms of length $k$, then one of the following holds:

  - $(n, x, a) = (m, y, b)$ and $k=0$
  - there exist $(n', x', a')$ and $(m', y', b')$ with $(n', x', a') <=_(s d) (n, x, a)$ and $(m', y', b') <=_(s d) (m, y, b)$,
    and a zigzag $(n',x',a') ~ (m', y', b')$ of length
    strictly less than $k$.
]
#proof[
  Suppose we have a zigzag
  #align(center,$(n,x,a) -> (n_1, x_1, a_1) <- (n_2, x_2, a_2)... (n_k, x_k, a_k) -> (m,y,b)$).

  Call the morphisms in the chain $f_1, ... f_(k+1)$. Each $f_i$ has a factorization as
  $t_i circle.small s_i$ where $s_i$ is surjective and $t_i$ is injective.
  Write $u_i$ for the codomain of $s_i$ (domain of $t_i$). Then by construction
  $u_1 <=_(s d) (n, x, a)$ and $u_(k + 1) <=_(s d) (m, y, b)$.

  Depending on the orientation of arrows in the graph, we have one of the following situations:
  - for all $i$, $1 <= i <= k$, if $i$ is odd then $(n_i, x_i, a_i)$ is the 
    codomain of two injective morphisms $t_i, t_(i + 1)$, and if $i$ is even
    then $(n_i, x_i, a_i)$ is the domain of two surjective morphisms $s_i, s_(i + 1)$
  - for all $i$, $1 <= i <= k$, if $i$ is even then (...) else if $i$ is odd then (...)

  For concreteness we will consider the first case, the second case is similar.
  By lemmas we have already proved,
  - for odd $i$, the cospan $(t_i, t_(i+1))$ can be completed to
    a commutative square with a span $(t'_i, t'_(i+1)$ with common domain $v_i$
  - for even $i$, the span $(s_i, s_(i+1))$ can be completed to a commutative
    square by extending it with a cospan $(s'_i, s'_(i + 1))$ with common
    codomain $v_i$

  It is now clear by construction that $v_1 <=_(s d) u_1$ and $v_k <=_(s d) u_(k + 1)$.
  There is now a zigzag of length $k-1$ joining $v_1$ to $v_k$, where
  $f'_i : v_i -> v_(i+1)$ when $i$ is odd, $f'_i : v_(i+1)->v_i$ if $i$ is even,
  where $f'_i = s'_(i + 1) circle.small t'_(i + 1)$ (the same definition is
  applicable regardless of whether $i$ is even or odd).
]

#theorem[
  Let $X$ be a simplicial set, and let $P : op(Delta_(s d)) times Delta_(s d) -> Set$
  be the functor associated to its geometric realization.

  Each connected component of the dinatural category of elements $el(P)$ has a unique minimal
  element with respect to the $(<=_(s d))$ ordering.
]
#proof[
  Let $(n,x,a)$ be an object. Forgetting $(n,x)$, by a previous theorem there is a unique least pair
  $(n_0, x_0)$ and a surjection $f : n -> n_0$ such that $X(f)(x_0) = x$, and $x_0$ is nondegenerate.
  Then $(n_0, x_0, F(f)(a)) <=_s (n, x, a)$.

  Now, forgetting $x_0$, there is a unique least pair $(n_1, a_1)$ and an injection $g : n_1 -> n_0$
  such that $F(g)(a_1) = F(f)(a)$. Then $(n_1, X(g)(x_0), a_1) <=_d (n_0, x_0, F(f(a))$.

  We can repeat this process, and it eventually terminates, yielding a triple $(m, y, b)$ where
  $y$ is nondegenerate and $b$ is an interior point of $F(m)$.

  If $(n,x,a)$ and $(m, y, b)$ are both minimal elements of the equivalence class,
  suppose they are connected by a zigzag of length $k$.
  By induction on the previous theorem statement, there is a single element $(n', x', a')$
  such that $(n',x', a') <=_(s d) (n, x, a)$ and $(n', x', a') <=_(s d) (m, y, b)$.
  But $(n,x,a)$ and $(m,y, b)$ are both minimal, so these must be equalities.
]

#theorem[Let $X$ be a simplicial set. The points in the geometric realization of $X$ are in bijection
  with triples $(n, x, a)$, where $a$ is a convex linear combination on $n$ points
  which is not zero at any point, and $x$ is a nondegenerate $n$-simplex.
]

This characterization is not too bad, but it suffers from the slight
defect that we have forgotten the topology on the simplices in order
to perform this analysis, which is unfortunate. Thus, for all our
work, this has not told us much about the topology of these points.
This theorem is similar to theorem I.2.10 of Manin & Gelfand,
but that theorem captures some topology in addition to simply
classifying the points in the geometric realization

For this reason it is interesting to try and pursue another approach
which will let us prove the theorem in Manin and Gelfand.

Let $j : bb(N) -> Delta_(s d)$ be the obvious inclusion functor. Let
$G : bb(N) -> Top$ be the functor sending each $n$ to the interior of
the $n-1$-simplex, where the interior of a point is regarded to be the
point. There is a natural transformation of functors $s : G => F j$.

If $X$ is a simplicial set on $Delta_(s d)$, then let $Y : bb(N)-> Set$
be defined so that $Y_n$ is the set of all maximal nondegenerate simplices.
There is a natural transformation of presheaves $t : Y => X j$.
The pair $(s, t)$ together determines a morphism between the weighted colimits
$WC(Y, G) -> WC(X,F)$. Now, we can use the same analysis as before to prove
that this map is bjiective.

= Geometric realization of a bisimplicial set

In this section let $Delta_(s d)$ be the simplex category, whose
objects are finite ordinals $n = {0,...,n-1}$ and whose morphisms are
monotonic but not necessarily injective maps between them. (Recall
that $n = { 0, ... ,n-1}$ is the standard ZFC encoding of the finite
ordinals.)

Let $F : Delta_(s d) -> Top$ be defined by $F(n) = Delta^(n - 1)$,
if $f : n -> m$ then $F(f) : Delta^(n-1) -> Delta^(m-1)$ is defined by
barycenteric coordinates, i.e., $F(f)(sum_(0<= i < n) alpha_i v_i) = sum_(0 <= i < n) alpha_i f(v_i)$.

Note the difference in indexing: $Delta^n$ traditionally denotes the $n$-dimensional simplex,
which is the convex hull of $n+1$ points in Euclidean space. A triangle (a 2-dimensional shape)
is the convex hull of three points in the plane. Traditionally, in algebraic topology,
authors write $[n]$ for the set ${0,...,n}$, that is, in ZFC $[n] = n+1$.

Write $|X|$ for $R_F (X) = WC(F, X)$, the
realization of the simplicial set $X : op(Delta_(s d)) -> Set$.

#definition[Face map, degeneracy map][
  Let $n,i$ be natural numbers, with $0 <= i <= n$.
  
  Define $sigma_i : n+2 -> n+1$ to be the unique surjective
  morphism in $Delta_(s d)$ which hits $i$ twice,
  i.e., $(sigma_i)^(-1)(i) = { i, i + 1}$.
  $sigma_i$ is called a *degeneracy map*.

  Define $delta_i : n -> n + 1$ to be the unique injective
  morphism in $Delta_(s d)$ whose image does not contain $i$.

  Let $X : op(Delta_(s d)) -> Set$. If $X$ is clear from context,
  then we write $s_i$ for $X(sigma_i)$ and $d_i$ for $X(delta_i)$.
  
  If $x in X(n + 2)$,
  then $x$ is said to be *degenerate* if it is of the form $s_i (y)$
  for some $y$, and *nondegenerate* otherwise.

  $x$ is *maximal nondegenerate* if it is nondegenerate,
  and $d_i (y) = x$ only if $y$ is degenerate.
]

#theorem[
  $|y(n)| = Delta^(n - 1)$
]
#proof[This follows by general nonsense about the realization. Manin and Gelfand
  assign it as an exercise in paragraph I.2.5.
]
#theorem[
  $|y(n) times y(m)| = |y(n)| times |y(m)|$
]
#proof[
  This is proved in Manin and Gelfand, the proof is the majority of Chapter I.3.
  You may need to consult the book, but the following should get you started.

  Hint: Try starting by showing that $|y(2) times y(2)|$ is homeomorphic to a square,
  and that $|y(2) times y(3)|$ is homeomorphic to a triangular prism.
  
  Hint: You will probably need to use I.2.9 - I.2.12.

  Hint: Start by counting the maximal nondegenerate simplices in $y(n) times y(m)$.
  Give them a nice naming scheme to keep track of them.

  Of these, which ones share a face in common: given two maximal non simplices $a, b$,
  we have $d_i a = d_j b$ for some $i, j$?
]

Bonus exercise: Characterize the geometric realization described in I.3.2(b) as a coend.

Bonus exercise: Recall that in *Top*, for a compact Hausdorff space
such as $Delta^n$, the set of maps $Delta^n -> X$ can be endowed with
a topology (the compact-open topology) which makes $(-)^(Delta^n)$
into a right adjoint to $Delta^n times (-)$. From this point of view,
there is a kind of *enriched nerve* functor $N_F : Top -> [Delta_(s
d)^op;Top]$, which sends each topological space $Y$ to the *simplicial
space* of singular simplices in $Y$. Prove that the coend of I.3.2.(b)
gives a universal arrow from a simplicial space $X$ into the enriched
nerve functor $N_U$; i.e., the "fat geometric realization" is a kind
of "enriched weighted colimit".


= Left Kan extensions in homological algebra

Let $Ch(Ab)$ be the category of (non-negatively graded) chain complexes of Abelian groups.

Let $I$ refer to the chain complex $0 -> bb(Z) -> 0$ whose value at zero is $bb(Z)$ and which
is zero elesewhere.

#theorem[The tensor product of chain complexes makes $(Ch(Ab), times.circle, I)$ into a *monoidal category.*
]
#proof[
  Look this up in any reference or prove it yourself.

  You do not have to check coherence conditions (pentagon law and
  triangle law) but you should check that the associator and unitor
  isomorphisms are chain maps.

  The associativity isomorphism $A times.circle (B times.circle C) tilde.equiv (A times.circle B) times.circle C$
  and $I times.circle A tilde.equiv A, A times.circle I tilde.equiv A$ should be easy enough to write down;
  check that these are chain maps (they preserve degree).

  // For the symmetry isomorphism $C times.circle D tilde.equiv D times.circle C$, you send
  // $c_i times.circle d_j |-> (-1)^(i j) d_j times.circle c_i$ (where $c_i in C_i, d_j in D_j$).
  // Check that the $(-1)^(i j)$ is necessary for the symmetry isomorphism to be a chain map.
]

We will take the point of view that the elements of $C_n$ at degree $n$ represent $(n-1)$-dimensional simplices,
because the $(n-1)$-dimensional simplex is the convex hull of $n$ points. For example,
- a unit interval is one-dimensional, it is the convex hull of two points
- a point is zero-dimensional, it is the convex hull of one point
- the empty space is (-1)-dimensional, it is the convex hull of the empty set of points.

By the *singleton* chain complex $Delta^0$, I mean the chain complex

#align(center,$0 -> bb(Z) -> bb(Z) -> 0$)

which is only nonzero in degrees 0 and 1. The only nonzero map is the identity map $id : bb(Z) -> bb(Z)$.

Intuitively,
- the generator in degree 1 corresponds to the unique 0-dimensional simplex (the point of the singleton)
- the generator in degree 0 corresponds to the the unique (-1)-dimensional simplex (the canonical, unique map from the empty simplex to a space $X$)

Similarly, $I$ is the chain complex corresponding to the empty simplicial complex.

Notice that this complex $Delta^0$ is exact, its homology is zero. This is similar to how the reduced homology of the singleton $tilde(H)( * )$ is zero.
So, our chain complexes model the *reduced* homology of these spaces.

// #theorem[$Delta^0$ is a commutative monoid in $Ch(Ab)$.]
// #proof[
//   Exercise. You should
//   - construct a multiplication $mu : Delta^0 times.circle Delta^0 -> Delta^0$ and check that it's a chain map
//   - construct a unit map $e : I -> Delta^0$ and check that it's a chain map
//   - check that the multiplication law is associative, unital, and commutative (compatible with the symmetry isomorphism)
// ]

// #theorem[Universal property of $Delta_d$][
//   Let $(C, times.circle, I)$ be a strict monoidal category, i.e., one where the associator and left/right unitor isomorphisms
//   are identity maps. Let $M$ be an object of $C$ and let $e : I -> M$ be any morphism. We will refer to $(M, e : I -> M)$ as a
//   *pointed object.*

//   A *strict monoidal category with a distinguished pointed object* is a tuple $(C, times.circle, I, M, e : I -> M)$.

//   A *morphism of strict monoidal categories with distinguished pointed object*
//   $F : (C, times.circle_C, I_C, M_C, e_C) -> (D, times.circle_D, I_D, M_D, e_D)$ is a functor
//   $F : C -> D$ such that $F(A times.circle_C B) = F(A) times.circle_D F(B)$, $F(I_C) = I_D$, $F(M_C) = M_D$, $F(e_C) = e_D$.
// ][

// ]

#theorem[$(Delta^0)^(times.circle n)$ is the standard chain complex associated to the $n-1$-simplex as a simplicial complex.]
#proof[
  Exercise. In your answer, count the number of generators of $(Delta^0)^(times.circle n)$ in each degree, $0 <= k <= n$,
  and describe the differential $partial^k$ of $(Delta^0)^(times.circle n)$.
]

In the following, we let $Delta_d$ denote the "semi-simplicial category" whose objects are finite ordinals
and whose morphisms are injective monotonic maps. Recall that $Delta_d$ is a monoidal category
with tensor product $n times.circle m = n + m$.

Exercise: what does $times.circle$ do on morphisms of $Delta_d$?

#definition[Unit morphism in $Ch(Ab)$][Let $e : I -> Delta^0$ be the chain map defined as follows:
- $e_0  : I_0 -> (Delta^0)_0$ is a map $bb(Z) -> bb(Z)$; we define $e_0$ to be the identity homomorphism.
- $e_1 : I_1 -> (Delta^0)_1$ should be a map $0-> bb(Z)$; this must be zero.

It is easy to verify that $e$ is a chain map.
]
$e$ corresponds topologically to the inclusion map $emptyset -> Delta^0$.

#theorem[There is a functor $U : Delta_d -> Ch(Ab)$ (unique up to natural isomorphism) defined by the following criteria:
  - $U(1) = Delta^0$
  - $U(0) = I$
  - $U(0 -> 1) = e$
  - $U(n + m) tilde.equiv U(n) times.circle U(m)$, naturally in $n,m$
]
#proof[
  You do not have to prove uniqueness; just prove that there exists such a $U$.

  In your answer, explain in detail what $U$ does on an arbitrary
  morphism $f : n -> m$. You should prove that $U(f)$ is well-defined.
  You should establish that $U(id(n))= id(U(n))$ and that
  $U(g circle.small f) = U(g) circle.small U(f)$.

  Hint: if a complex morphism $f : n -> m$ can be broken down into the $times.circle$-product
  of simpler maps like $e$ and $id(1)$, we can define $U(f)$ in terms of $U(e)$ and $U(id(1))$.
]

#theorem[The singular chain complex of a topological space is a pointwise left Kan extension][
  Let $C : Top -> Ch(Ab)$ be the singular chain complex functor (see Hatcher, p. 108).
  Then $C$ is the pointwise left Kan extension of $U : Delta_d -> Ch(Ab)$ along $i : Delta_d -> Top$.
]

The proof is on the next page, I encourage you to try and prove this as a (hard!) exercise without looking at the proof.

#pagebreak()

#proof[
  We want to prove that $C(X)$ is the weighted colimit of $U$ with weights in the presheaf
  $N_iota (X)$.

  We start by defining a natural transformation
  #align(center,$eta : N_iota (X) -> N_U (C(X))$)

  We define this in degree $k$ as follows: if $sigma : Delta^(k-1) -> X$ is a singular $k-1$-simplex,
  then we define $eta_k (sigma)$ in in each degree $m$ as follows. The generators of $(Delta^0)^(times.circle k)_m$
  are in one to one correspondence with injective monotonic morphisms $g : m -> k$; we send the generator
  represented by $g$ to $sigma circle.small i(g)$. We omit the proofs that
  - this defines a chain map $(Delta^0)^(times.circle k)_m -> C(X)$
  - $eta$ is natural.

  It is now necessary to prove that $eta$ is universal among natural transformations $N_i (X) -> N_U (-)$.
  Therefore, let $A$ be an arbitrary chain complex, and $tau : N_i (X) -> N_U (A)$ a natural transformation.
  We propose to define a chain map $mu : C(X) -> A$ such that $N_U (mu) circle.small eta = tau$.
  Let $sigma : Delta^(k - 1) -> X$ be a singular simplex, regarded as a generator of $C(X)_k$.
  We define
  #align(center, $mu_k (sigma) = tau_k (sigma_k) (id_k)$)
  where $tau_k (sigma) : (Delta^0)^(times.circle k)-> A$ is a chain map, and $id_k$ is the
  canonical generator of $(Delta^0)^(times.circle k)_k$.

  It is necessary to prove that $mu$ is a chain map. So, let $sigma$ be a singular $n$-simplex,
  i.e., a generator of $C(X)_(k+1)$.  
$
  mu(d(sigma))
    &= mu(sum_i (-1)^i d_i sigma) \
    &= sum_i (-1)^i mu(d_i sigma) \
    &= sum_i (-1)^i tau_k (d_i sigma) (id_k) \
    &= sum_i (-1)^i tau_k (N_iota (X) (partial_i) sigma) (id_k) \
    &= sum_i (-1)^i (N_U (partial_i) (tau_(k+1) sigma)) (id_k) \
    &= sum_i (-1)^i ((tau_(k+1) sigma) circle.small U(partial_i)) (id_k)  \
    &= sum_i (-1)^i ((tau_(k+1) sigma) (U(partial_i) (id_k))  \
    &= (tau_(k+1) sigma)(sum_i (-1)^i U(partial_i) (id_k))  \
    &= (tau_(k+1) sigma)(d(id_(k+1)))  \
    &= d(tau_(k+1) (sigma)(id_(k+1)))  \
    &= d(mu(sigma))  \
$    
]

As an important note, one can replace the category $Delta_d$ in this exercise with
the simplex category $Delta_(s d)$, or $Delta_(s d g)$ (FinCard), and both $iota$ and $U$
can be adapted to handle the degeneracy maps and permutations. In both of these
cases, the pointwise left Kan extension of $U$ along $iota$ has a fairly nice
description which is closely related to the complex $C(X)$. All three chain complex functors
$C: Top -> Ch(Ab)$ give rise to the same singular homology theory, even though the chain complexes are not isomorphic.

= Abstract simplicial complexes

Abstract simplicial complexes are defined, for example, in Lee's _Introduction to Topological Manifolds_ (p. 153) and
in Spanier's _Algebraic Topology_, p. 108.

Both of these references define a morphism of ("abstract") simplicial complexes (an "abstract simplicial map").

#let ASC = [#math.bold("ASC")]

There is thus a a category of simplicial complexes $ASC$.

As a technical point about an edge case: the empty simplicial complex
is an abstract simplicial complex. It has no vertices, and no
simplices. (Each simplex is required to be nonempty, but one can have
an empty set of nonempty simplices.)

Let $Delta_(s d g)$ be the category whose objects are finite sets $n = {0,... n-1}$ (possibly empty) and whose morphisms
are all functions.

There is an inclusion functor $S : Delta_(s d g) -> ASC$, $S(n) = (n, cal(P)(n) - emptyset)$
(i.e., the vertex set is $n$ itself, the simplices are all nonempty subsets of $n$)

#theorem[The pointwise left Kan extension of $S$ along $S$ is the identity functor $ASC -> ASC$.]
#proof[Hard exercise.]

What does this mean? How do we interpret it?

= The etale space of a presheaf on a topological space

Start by skimming II.1 - II.3 of *Sheaves in Geometry and Logic* for some small background on sheaf theory.

Let $X$ be a topological space. Let $tau(X)$ be the topology of $X$ regarded as a poset category.

Let $Top\/X$ be the comma category of bundles over $X$ and commutative triangles between them.

Let $J : tau(X) -> Top\/X$ send the open set $U$ to the inclusion map $i_U : U -> X$.

This section is devoted to the study of the nerve-realization
adjunction arising from $J$. This adjunction is described in detail in
*Sheaves in Geometry and Logic*, Chapter II, sections 4-6; you may
reference this at any time. Many theorems here are proven in that
book; you can choose to try to prove them yourself as an exercise or
look for the proof in that book. (For background on sheaves, you can
skim II.1 - II.3, but this is not very important.)

The nerve $N_J$ is also called the *sheaf of sections* functor by Mac
Lane in II.4 and denoted $Gamma$. Describe $N_J$ as best you can and
think about it. When you are finished, read all of SGL II.4. Why is it
called the sheaf of *sections*?

"Compute" the realization of a presheaf $P$ on $tau(X)$. One can always give a very
general description of $R_J (P)$ as a set quotiented out by an equivalence relation;
try to be as concrete as possible to get intuition for the space $R_J (P)$.

// Suppose $P$ is the sheaf which associates to $U$ in $X$ the set of
// continuous functions from $U$ into $bb(R)$. If $a$ is a point in the
// space $R_J (P)$, can you describe what $a$ is or represents in terms
// of continuous real-valued functions on $X$?

Let $X= bb(C)$, and suppose that $P : tau(X)^op -> Set$ associates to
the open set $U subset bb(C)$ the set of holomorphic functions $U ->
bb(C)$ defined everywhere on $U$. Describe the space $R_J (P)$. How
would you describe the points of the space $R_J (P)$ concretely in
terms of holomorphic functions?

In "Sheaves in Geometry and Logic" II.5, $R_J$ is explicitly
constructed and referred to as $Lambda$; Theorem II.6.2 shows it has
the universal property of the weighted colimit. Try reading II.5 up to
the end of page 85 and then proving that $Lambda_P$ is homeomorphic to
your description of $R_J (P)$. (Mac Lane gives two examples of
$Lambda$ - for real-valued functions the space is not Hausdorff, for
complex-valued funct it is Hausdorff. You should understand the proofs
that one is Hausdorff and the other is not.)

Suppose $p : E -> X$ is a covering space map. Prove that $R_J (N_J (p)) = p$.
(For concreteness start with familiar covering space maps such as $bb(R) -> S^1$.)

As an example application of this theorem, consider the covering space map $p : bb(C) -> bb(C) - { 0 }$ given by $z |-> e^z$.
Then $p$ is a covering space map. $N_J (p)$ could be simply called "$ln$";
as on each open set $U$, it returns the set of branches of the natural logarithm functions
(i.e., inverses to the exponential function)
which are globally definable everywhere on $U$. $R_J (ln)$ is then a Riemann surface,
fibered over $bb(C) - { 0 }$, which allows us to represent these various
branches of the natural logarithm as sections of the bundle.

Let $P$ be an arbitrary presheaf on $X$. Prove that for every point $a$ in $R_J (P)$,
there is a small open neighborhood $U$ of $a$ such that the projection map $pi : U subset R_J (P) -> X$
is an open subspace embedding (i.e., it's homeomorphic onto its image).

Read as much of II.5 and II.6 as you want and study the proofs of whatever theorems you find interesting.
