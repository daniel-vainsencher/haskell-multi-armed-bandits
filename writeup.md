General
=======

The project idea is to use ideas from machine learning, to treat the
inlining decisions made in an optimizing compiler (GHC) as a planning
problem, hopefully resulting in higher performance output
programs. This could be useful in scenarios where compilation effort
is less important than runtime performance; we propose two such
scenarios.

In the first consider cross compilation where the target is a highly
power constrained device, such as a battery operated sensor network
node. In the second, consider a long running service where response
latency is very important, such as algorithmic trading. In either
case, it is reasonable to expend considerable computational effort on
compiling the most efficient program for the releant criterion. In the
sensor network case we might distinguish a preparation phase after
which the program is deployed to the units and the units to the field,
and all that matters is how efficient a program we achieved before
deployment. In the low latency service, in contrast, we might imagine
reserving some hardware resources for recompiling a program in the
background, using continuous feedback from operations.

An important technical difficulty is that the cost of optimal planning
is generally exponential in the size of the problem, as measured by
the number of interdependent decisions that must be made. We thus
propose to decompose the inlining problem in a way that is adapted to
the program structure, resulting in multiple more managable planning
problems. We address also some possible efficiencies in working on
these multiple problems at the same time.

Contents:

1. Explain the planning algorithm view of problems.

2. Present one simple way to view inlining decisions as a planning
problem.

3. Present a subclass of planning algorithms based on multiarmed
bandit algorithms.

4. Present an extension called isolated subproblems to planning in the
context of GHC and inlining.

Planning algorithm view of problems
===================================

We model problems as an iterated interaction with an abstract
environment. In each interaction, we specify a plan of action
(ActionSpec a, where a is the type of a single action).

> data BanditProblem m a = BanditProblem { bpPlayAction   :: ActionSpec a -> m (BanditFeedback a)
>                                        , bpIsDeterministic :: Bool }

In the common case we may define:

> ActionSpec a = [a]

So that a plan is simply a list of basic actions.

The environment carries out this plan of action in a monad m (maybe by
running a program with our plan as its input), and gives us some
feedback.  In the common case, BanditFeedback is BanditFeedbackSimple
where

> data BanditFeedbackSimple a
>      = BanditFeedback { fbPayoff :: Float, fbActions :: [a] }

Here feedback is a payoff we would like to maximize, and a list
(possibly empty) of further actions that are legal at the end of the
given plan.  It is reasonably common for the payoff to be somewhat
noisy, perhaps due to measurement error, other noise, or even
fundamental randomness of the environment, such as when playing
backgammon.

The simplest algorithm play an increasing sequence of random actions,
ignoring the feedback. A cheap but potentially useful greedy algorithm
might try for each given prefix of actions two of the possible next
actions, and immediately commit to the better of those two. A more
expensive algorithm would exhaustively try all plans of length k
before committing to only the first action in the optimal subplan, and
then repeat. In a random environment, we might run each action plan
several times in a row and use the average result as a proxy for the
expected goodness of the plan. There is a very wide literature on
planning algorithms in different contexts, we will give a description
of the one we have tried and some pointers later. However when action
plans are simple lists, the space of possible plans is a tree, and
planning algorithms generally create a partial map of this tree in
memory to document their findings so far.

Now consider a game of the following form:

    ~~~
    For t=1 .. T
        Planning algorithm specifies an action plan A_t.
        Environment gives feedback: payoff p_t and possible actions A_t.
    ~~~

At the end of the game, the planning algorithm receives either
$max(p_t)$ or $sum(p_t)/T$, corresponding to two common and distinct
situations, both relevant to this domain. Denoting the gain (of
whichever form) $V_T$, a good algorithm is one such that the average
regret

$R_T=V^* - V_T$

approaches 0 quickly, where $V*$ is the payoff for an optimal action
sequence (which we assume for moment exists). Under suitable technical
restrictions, good algorithms achieve

$R_T = O(n*log(T)/T)$

for algorithms based on the UCB or optimism in the face of uncertainty
approach, or

$R_T=O(sqrt(n/T))$

for algorithms based on Exp3 or unbiased estimator approach.

Where $n$ is a measure of the size of the problem, for example the
number of possible action sequences. Note that if $R_T$ indeed
approaches zero, that implies behaviour that is close to optimal, so
this is certainly a guarantee worth having. Unfortunately, for a
planning problem $n=2^d$ where $d$ is the depth of the tree of
possible actions, even in the case where each decision has just 2
options. Therefore obtaining algorithms with meaningful guarantees
requires further assumptions on the problem; we instead turn to a
particular real problem, and look for mere useful algorithms, only
inspired by optimal ones.

The inlining problem as a planning problem
==========================================

The simplifier pass in the compiler GHC iterates over a Core
representation of a Haskell program. When it encounters a function
application

> f x y z

with the function definition in scope, say:

> f = \a b -> a+2*b

it has the possibility of inlining it to produce

> (\a b -> a+2*b) x y z

This brings the definition of the function close to a particular
context in which it is called, which may enable some further
simplifications: compile time arithmetic, removal of high-order
programming over head etc.

Then the most natural way to pose inlining as a planning problems is
the following:

> runtimeInliningProblem :: BanditProblem IO Bool 
> runtimeInliningProblem = BanditProblem 
>   { bpPlayAction = <compile the program, deciding whether to inline 
>     according to the given list of Bools; when the list of Bools 
>     runs out, use some default (yes, no, random, current heuristics... 
>     etc). Run the compiled program on some example input that we 
>     care about, and return as the payoff the negation of total run time. 
>     The list of available actions is [True,False] if the list of Bools 
>     ran out before the program was simplified, [] otherwise.>
>   , bpIsDeterministic = False {- Because runtime is somewhat random -} }

This requires a full compile/link/run cycle for each numerical
feedback. It also poses the requirement that a benchmark (example
input) is available, and in particular, that the program really is a
complete standalone program, and not a module. We are thus led to
consider another way to pose the inlining problem. At the moment GHC
has a set of simple heuristics for deciding whether to inline a
particular function at a particular point. If we could extract a
simple function over compiled programs that expresses those
preferences, and use that as feedback, we would not need a
benchmark. In fact, GHC already counts simplifier events in
SimplCount, and some of those (such as dead code elimination: the
removal of a binding that is no longer referenced anywhere) counts the
kind of improvements that we hope inlining will result in. This leads
us to:

> simplificationCountInliningProblem :: BanditProblem CoreM Bool 
> simplificationCountInliningProblem = BanditProblem 
>   { bpPlayAction = <SimplCore.simplifyPgm, deciding whether to inline 
>     according to the given list of Bools; when the list of Bools runs 
>     out, use some default (yes, no, random, current heuristics... etc). 
>     Compute the inner product <simplCount,weightVector>, subtract 
>     (coreBindsSize $ mg_binds guts) and that is the payoff. The list 
>     of available actions is [True,False] if the list of Bools 
>     ran out before the program was simplified, [] otherwise.>
>   , bpIsDeterministic = True {- Because compilation is repeatable. -} }

Where we take weightVector to be positive for good events, zero
otherwise.

Then an effective planning algorithm can be expected to eventually (as
the number of bpPlayAction calls allowed goes to infinity) find a tape
of inlining decisions that maximizes a linear tradeoff between counts
of desirable optimization events and the total code size.

A style of planning algorithm
=============================

If we restrict the planning problem to action plans consisting of a
single action, we arrive at the very well studied and very active
field of multi armed bandit (MAB) problems, so called for their
resemblance to the following scenario: you arrive at a casino with $k$
distinct slot machines, and $T$ play tokens. When you insert a token
into a machine and pull the lever it has a probability $p_k$ of
outputting a coin. Such a machine is often called a one-armed-bandit,
hence the name for the complete scenario. Of course our goal is to
maximize the number of coins we have when the tokens are spent, but
the probabilities $p_k$ are not known in advance. So that one must
trade off between exploitation (spending tokens on the machine that
has behaved best so far) and exploration (spending tokens on machines
that we might not yet know well enough).

A simple algorithm resolves the resource allocation problem with a
coin:

1. With probability $p$, choose an action at random, and update the
empirical estimate of the mean reward for that action (aka: its
average reward so far).

2. With probability $1-p$, choose an action with maximal average
reward.

More powerful MAB algorithms include Upper Confidence Bound based
algorithms such as we used and Exp3, which always chooses the next
action randomly, but updates the probabilities using an unbiased
estimator of the reward vector of all actions.

The interesting property of bandit algorithms for our purposes, is
their robustness to low quality feedback: feedback may be randomly
noisy and in some senses even arbitrarily badly behaved, but as long
as the feedback is bounded (or at least thin tailed), theoretical
guarantees can be made about their average regret $R_T$ when the
reward is of form $sum(p_t)/T$.

Given a good algorithm A for solving MAB problems, a credible
algorithm for solving planning problems might:

1. Construct the directed rooted map tree, where a path from the root
corresponds to an action plan that has been tried, and that summarizes
the corresponding feedbacks.

2. At each node of the tree, corresponding to a plan prefix that
arrives at it, use an instance of algorithm A to choose the next
action (expanding the tree by one or more nodes at every turn).

3. Given a reward for executing a plan, update all nodes in the tree
along the path corresponding to this plan.

This is the essence of a class of algorithms whose predecessor is UCT
(Upper Confidence Trees), which has proved a great improvement to the
performance of mechanized play of the game Go.

Isolation in planning
=====================

In simplifying a program, GHC often encounters hundreds of inlining
decisions. Treating each decision as conditioned on all previous
decisions has two unfortunate implications:

1. Any change in an early decision means reexploration of all later
decisions. Therefore naturally, later decisions receive far less
attention than early ones under almost any algorithm.

2. General optimal planning of a _deep_ problem, producing a sequence
of hundreds of decisions, is intractable without further strong
assumptions.

This treatment is also unappealing in ignoring the structure of the
program. Consider the following fragment:

    ~~~
    let v1 = expr1
        v2 = expr2
    in < ... v1 ... v2 ... > 
    ~~~

 
If for some reason we knew that v1, v2 will not be inlined, then we
can in principle consider the simplification of expr1 and of expr2 as
independent subproblems: how we compute one does not affect the
efficiency of different ways to compute the other. Decomposing
planning problems is very beneficial: complete exploration now
requires feedback about $2^m_1+2^m_2$ possibilities instead of
$2^(m_1+m_2)$, where $m_i$ is the number of decisions to be made in
$expr_i$. Another benefit can occur if it is less costly to obtain
feedback about decisions in the context of just expr1 rather than the
complete program. Recall that to obtain a feedback about any decision,
we run the simplifier and take a linear combination of its counts and
the resulting expression size. In fact we are able to take note of
what subproblem we are working on, and compute a feedback for each
subproblem separately, in one run of the simplifier over the
program. Thus the cost of complete exploration becomes $2^m$, where
$m$ is the number of decisions made in the most complicated of the
independent subproblems.

These potential benefits highlights our assumption: do any such
situations arise? They seem not to arise naturally. For example
consider:
 
    ~~~
    let func = \ a b -> ...
    in func expr1 expr2
    ~~~


If func cannot be inlined (for example, it is a library function, and
its source is not given), then expr1 expr2 seem independent. But a
rewrite rule could remove the function and render expr1 and expr2
relevant to one another again. Therefore we have begun exploring the
possiblity of creating independencies.

Suppose in the first example, that we distinguish between the
definition of v1, which describes how it is computed when referenced,
and its unfolding, which is the code we insert when inlining v1. This
is a distinction GHC already makes; at the moment either the two
correspond closely, or the unfolding is unavailable (then inlining is
ruled out). We instead use the planning approach only in simplifying
the definition of v1, without updating the unfolding (in fact, at the
moment we leave the unfolding completely unsimplified, but this is not
an essential feature and probably a bug).

Then the definition can be simplified in isolation from the rest of
the program; posing a less deep problem, it can be solved closer to
optimality, and the necessary feedback is obtained at no additional
cost. The improved definition is used wherever the name is referenced
originally and not inlined. The remainder of the program is now
simplified with respect to the fixed unfolding; if a reference to the
variable is inlined, it is the unfolding that replaces it. To the
extent that this occurs, optimizing the remainder of the program will
still include decisions about the variable; however the decisions
about the definition itself do not contribute to the depth of the
remaining problem.

