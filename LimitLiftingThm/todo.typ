#import "@preview/cheq:0.2.2": checklist
#show: checklist

Structure of the paper

= Friday, 2025-11-28

Today I tried proving the "exponential" theorem in the context of a
double category of lax double functors, *pseudo* natural horizontal
transformations, and so on. My conclusion from this exercise is that
in general, there is no Cartesian lift of a pseudonatural horizontal
transformation whose domain is a horizontally strict functor. If we
were willing to introduce a new definition of a *functor* which was
not horizontally strict, then this problem could be addressed. I
regard this as out of scope. The second solution, which is more
straightforward, is to adopt the assumption that the local vertical
fibrations (i.e. the local fibrations of $bold("V")_0(p)$)
are *split* and that the splitting structure commutes
with the horizontal unit and composition law. This condition
is easy to write down but it seems strange to
ask for a splitting satisfying strictness conditions with respect
to the horizontal unit and composition law given
that the horizontal unit and composition are themselves
not even strictly associative and unital. Funny.

Second, I returned to understand the proof of the main theorem and
what the current flaw is. I think the proof would probably be correct
if we had a proper 2-fibration, but we don't. Here, there are
two ways to solve the problem:
- make additional assumptions on $p$ so that we have a proper
  exponential fibration
  (I think that assuming the original double fibration is a split fibration should be enough
  to fix the problem with modifications)
- accept that the pullback of a natural transformation along a modification will be
  pseudonatural in general, and see if there is a way to adopt the proof to account for this.

*TODO*: my definition of "preserving limits"
asks for a condition on 2-cells. I'm not actually sure if that
is relevant. I should resolve that. Is it provable already?

Let me think. Does the proof really need anything extra?

No, I don't think so. So, we might have solved the problem. I'll try
this tomorrow and we'll see if it works.

