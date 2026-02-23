#import "/preamble.typ":*
#import "/category-theory-notations.typ":*

The purpose of this document is to be a research diary for
this "profunctor of lifts" project.
We will outline the scope of the project,
we will give some motivation.

As the project evolves we will also evolve the scope of the paper.

= Outline/introduction

In this paper we are interested in the concept of a
"double-categorical lifting operation" which has been given by Bourke and Garner in their paper
"Algebraic Weak Factorization Systems I", Section 6 : Cofibrant Generation by a Double Category.

The concept seems to us very natural, and it should be regarded as fundamental in the study
of lifting and extension operations. However, the characterization given by Bourke and Garner
is using flat equations; the notion of a lifting operation is not characterized in
"categorical" terms, in a way that puts these equations in context by relating them to
other known categorical constructions.

The principal goal of our paper to give a categorical characterization of what these things are,
by expressing them as a kind of limit or end.

If $C$ is an ordinary 1-category, and $J, K$ are $1$-categories, and $U : J -> C$, $V : K -> C$
are 1-categories, then there is a profunctor $Hom(cat:C, U(-), V(-)) : op(J) times K -> Set$.

We might think that the notion of "double-categorical lifting operation" is related
to a kind of Hom-profunctor $Hom(cat:C, U(-), V(-)) : op(bb(J)) arrow.r.struck op(bb(K))$.

It turns out to be a bit more subtle than this, but the difficulties can be resolved by passing to three
dimensions and using a notion of triple categories and triple profunctor.

A concept of triple profunctor has not appeared in the literature and so much of our paper develops this notion,
with the intent of supporting our description of these double-categorical lifting operations.

Our basic framework is the notion of intercategory given by Grandis and Pare.
