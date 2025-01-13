---
title: Ten Years of Blog
date: 2025-01-10
---

I noticed as I was reviewing [last year](https://www.philipzucker.com/2024_year/) that today is the 10 year anniversary of my blog. WOO! 🎉

My first post on Jan 10, 2015 was stunning <https://www.philipzucker.com/getting-wordpress-to-work/> to say the least.

# Thoughts on Blogs

## Get it out there

I think generally people are too secretive about their work. It's insane to me the number of github projects that are in private mode that will never go public, even if they do have some MVP that's kind of interesting.

If you think you should wait, consider that no matter how dumb something you write is:

- A. no one cares  
- B. if they could care, say it often and early so someone could hear it.

This is partly again my personality. I can sprint a bit, but long hauls with no external validation are hard/impossible. If you really can work on something for 5 years and then put it out, more power to you.

If you are starting a blog, unless you are already famous somehow, you do not have an audience. Even if you put out world shaking shit, no one will read it. So don't worry about it. Just put stuff out. You need surface area for anyone to find you.

## But I've got nothing to say

Doesn't matter.

[Action precedes motivation](https://www.youtube.com/watch?v=W3I3kAg2J7w&ab_channel=3Blue1Brown)

The posts are somewhat interesting to your future self no matter what.

The writing cements knowledge now and the act of fleshing things out can discover questions you didn't realize could be had when you left information confident feeling but actually murky.

Everyone can write something interesting for someone on a similar rung of the ladders of learning. No, I can't write a post that is all that interesting to a world expert. But you can explain things in a way that only a person with fresh recent eyes can do. Explanation ability does not grow monotonically. I don't know how to explain addition to a 5 year old anymore. I don't always know how to keep myself entertained writing about something I learned a decade ago. Do it fresh.

## How I write notes

I have organically shifted or discovered techniques to takes notes or find some kind of angle to grind over the years.

I open files for broad areas and have scattered sections about thoughts or little ideas from what I'm reading. I allow chaos. I try to write little snippets. When I come back, I always find I have written less notes than I thought I did. Keeping the links I was looking at is helpful. My memory is also always weaker than I thought. Even having an outline of headers saying key subjects is a really useful mindmap.

I've moved towards having ideas centrally located in my blog repo. I used to have more sketch ideas done in folders, but I lose track of them as I've moved computers and such. 10 years gives me perspective on what can be maintained or not. Go simple. Own your content. Being on a platform is ultimately a disaster if you want to keep your stuff for 20 years. Being in a single folder you can git repo or copy around is important. You will be less careful and vigilant than you think. I think Jekyll is on its way to collapsing in the next 15 years or so, but at least it's plain text. It wouldn't be a _disaster_ to just serve the plain files. I would like my blog to stay up another 15 years after I die. It's kind of hard to achieve that.

For a while, I used markdown and a slightly altered VS code plugin that could shell them out <https://github.com/philzook58/vscode-markdown-code-runner> to the language in question. It gives you kind of a low tier jupyter experience. About a year ago I transitioned back into jupyter notebooks. I don't like they are not plain text and they are hard toi copy and paste. Nevertheless, the `%%file` and `!` bash execution capabilities mean I can work in any language and have it store and record the output of my commands. This is very useful. Getting into the habit of just slapping stuff into `/tmp` has been a useful way to operate. Trying to pipe everything or actually use python's subprocess or file creation to go multilanguage is too laborious. I even use this style for low level C examples and such. It's nice to know I've included everything needed in the blog post by construction. Another advantage of jupyter is that I can paste a colab <https://colab.research.google.com/github/philzook58/philzook58.github.io/blob/master/pynb/2024-11-18-sql_graph_csp.ipynb> link for people to try it themselves. Just put the github path at the end there.

I think if I could stand org mode it might be a nice option.

## Has My Blog Generated Opportunities

Mostly no. It has not gotten me any jobs or made me any money. But it has started a few conversations. More importantly, I derive a sense of purpose and accomplishment from it. It gives me concrete breadcrumbs and something to grind on. Waiting for inspiration or passive learning do not work well.

# A Retrospective

## 2015-2016

It was originally a wordpress instance that I put on nearlyfreespeech, a cheap hosting service. It's too bad but I don't remember the initial impetus for making it. Maybe [Dan Piponi](http://blog.sigfpe.com/)'s blog was an influence. I loved that thing. It slowly rotted over the next couple years until I migrated it to Jekyll and github pages in 2020 <https://www.philipzucker.com/i-moved-my-blog-from-wordpress/>. I never strictly speaking turned off the old wordpress site. It exists in a completely broken form. <https://philzucker2.nfshost.com/>

I was in grad school for physics at the time, a decade younger. In the process of realizing I wasn't going to make it big there, despite the greatest efforts I knew how to give. That perhaps deserves a post on its own. This left a wound I still struggle with. It gets better all the time though. Your twenties can be a tough time where "promising" stops being good enough and it needs to start actualizing. Many realities of life settle in. I also had a blast though, the echoes of which still reach to today. It's a mix.

In the olden blog times, I thought it was a useful endeavor to explain how to install software, which is often a challenge. I think at some point I got good enough at guessing how to fix broken builds that it didn't seem worth making a whole post on anymore.

This also shows from the beginning that I felt that there was no scope too small to be worth a post. Keeping flow is important.

I had recently heard of Haskell at this point and was Haskell curious. I can see some topics that I still want to write posts about or understand better. I learned BASIC as a kid out of some 1$ library sale book and had fiddled a bit with Java, matlab, and arduinos in college. I learned python during grad school and was in love with using numpy for linear algebra simulations of waves and things after watching Gilbert Strang's Computational engineering lectures <https://math.mit.edu/~gs/cse/> . At 2015 though, I really hadn't been exposed to much computer science or logic in the scheme of things.

I was interested in arduino robots, opencv, physics simulations, 3d printing, HAM radio / SDR, Functional programming.

I can see seeds of what i still do in terms of taking esoteric seeming Haskell stuff and how I translate it into python.

- I still want to make this haldane gyrator circuit <https://www.philipzucker.com/topologically-non-trivial-circuit-making-haldane-model-gyrator/>
- <https://www.philipzucker.com/python-generators-and-infinite-power-series/> Lazy power series is still a cool trick. See Power serious by Doug McIlroy <https://www.cs.dartmouth.edu/~doug/powser.html>
- <https://www.philipzucker.com/random-potentials-and-qft-i/> Single particle quantum mechanics in a random potential is in some respects very similar to quantum field theory., except also more amenable to use monte carlo as ground truth. Also related to scattering by random media. I could like to explore this more
- <https://www.philipzucker.com/hash-vectors-interacting-particles/> Hash vectors is an idea that has stayed relevant. Very simple idea, you can have interestingly structured indices and it's useful if you use dictionaries for . This is almost a difficult thought to have from a low level high performance or numpy perspective I think. You're too used to using integers to label your basis.
- <https://www.philipzucker.com/using-z3-solve-simple-logic-puzzle/> an early z3 blog post

I was doing more projects in meat space. That is good for the soul.

## 2017-2019

Here I was graduating and starting my first job at Lincoln Labs.

- I was pretty pround of my topological quantum computing in Haskell series. <https://www.philipzucker.com/a-touch-of-topological-computation-3-categorical-interlude/> It felt like a high point of a lot of learning. I've been meaning to revisit this stuff.
- I was also proud of reverse mode differentiation is kind of like a lens. <https://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/> I think it's a pretty straightforward functional programming explanation of reverse mode AD. I got weirder with it <https://www.philipzucker.com/neural-networks-with-weighty-lenses-dioptics/> . The lens pattern is useful for many 2-3 pass algorithms. <https://www.philipzucker.com/uniform-continuity-is-kind-of-like-a-lens/> <https://www.philipzucker.com/a-sketch-of-gimped-interval-propagation-with-lenses/> . You can use similar implementation techniques to reverse mode AD to implement these things too. I think for example, the exact reals are kind of like a lens. You ask for an answer of some allowed error, that propagates backwards through the tree to ask the sources for accuracy, and then the calculation propagates back though. Each intermediate piece needs to save how much error it needs.
- Physics and convex optimization <https://www.philipzucker.com/solving-the-ising-model-using-a-mixed-integer-linear-program-solver-gurobi/> are topics that I think could have more interconnect. There barrier between solvability isn't linear to nonlinear, it's convex to nonconvex. A convex hamiltonian for a field has a unique minimum and is thus perfectly tractable in some sense, even if there isn't a closed form solution. <https://www.philipzucker.com/solving-the-xy-model-using-mixed-integer-optimization-in-python/> <https://www.philipzucker.com/the-classical-coulomb-gas-as-a-mixed-integer-quadratic-program/>
- <https://www.philipzucker.com/nand2tetris-in-verilog-and-fpga-and-coq/> Doing nand 2 tetris using formal tools. Another ongoing project. Now I want to do it in [knuckledragger](https://github.com/philzook58/knuckledragger). <https://github.com/philzook58/nand2coq>
- I have a bunch of posts here about trajectory optimization. This was my optimal control and reinforcement learning phase. I was also quite into mixed integer programming solvers. Ben and I were building a cartpole. <https://www.philipzucker.com/cartpole-workin-boyeee/> Impressive stuff! The physical world is tough. I'm also impressed by how long we stuck with it and all the sorts of games I was playing with it.
- <https://www.philipzucker.com/gettin-that-robot-some-tasty-apples-solving-a-simple-geometrical-puzzle-in-z3-python/> another early z3 post

## 2019-2020

- <https://www.philipzucker.com/proving-some-inductive-facts-about-lists-using-z3-python/> Probably the start of what might end up being [knuckledragger](https://github.com/philzook58/knuckledragger). I only bring up knuckledragger so much now because it is my current fixation. We'll see what I feel about that in another 10 years.
- <https://www.philipzucker.com/annihilating-my-friend-will-with-a-python-fluid-simulation-like-the-cur-he-is/> This was a fun one. It's good to make interesting visuals.
- Was in a "category theory" phase. What I called category theory and what category theorists call category theory are pretty different. Basically, I liked modeling and writing DSLs in a combinator style, with a `compose` and `id` combinator. It was fun though. <https://www.philipzucker.com/i-gave-a-talk-on-executing-categories/> <https://www.philipzucker.com/categorical-combinators-for-graphviz-in-python/> <https://www.philipzucker.com/a-sketch-of-categorical-relation-algebra-combinators-in-z3py/>
- Learned a lot about partial evaluation for work. <https://www.philipzucker.com/metaocaml-style-partial-evaluation-in-coq/> We built a clone of sorts of Yallop and Kishnaswamis staged parser combinators  in Coq. <https://www.cl.cam.ac.uk/~nk480/parsing.pdf>  <https://github.com/draperlaboratory/parts> It was actually kind of fast (compared to ocaml baselines)! In a horrible hacky way. I really wish I hadn't felt uncomfortable posting about this more. There were lots of cool little things and I've since never been interested enough to revisit them. Write in the now. Don't wait.
- I read the algebra of programming book (freezing my tuckus off in patagonia. Hey, I live well!) and was quite impressed.  <https://www.philipzucker.com/lens-as-a-divisibility-relation-goofin-off-with-the-algebra-of-types/>  <https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/> . This post got pulled out of the graveyard a few months ago onb hacker news, which was interesting <https://www.philipzucker.com/linear-algebra-of-types/> <https://news.ycombinator.com/item?id=39873756>
- I really quite liked this idea of Linear Relations as an API to the schur complement and a way of talking about open circuits. <https://www.philipzucker.com/solving-the-laplace-equations-with-linear-relations/> <https://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/> <https://www.philipzucker.com/categorical-lqr-control-with-linear-relations/>
- <https://www.philipzucker.com/why-i-as-of-june-22-2019-think-haskell-is-the-best-general-purpose-language-as-of-june-22-2019/> a slightly shameful post that ended up on hacker news or something. A classic whining about language choice. I wouldn't particularly want to use Haskell anymore. I fell of using Haskell when I started my new job that was an OCaml shop and became burned out on trying to push functional programming on the unwilling. Hence my current strong focus on python.
- <https://www.philipzucker.com/flappy-bird-as-a-mixed-integer-program/> This was a fun model predictive control example. We busted this out in a weekend. So many reddit likes! We were riding high.
- <https://www.philipzucker.com/learn-coq-in-y/> I wrote a whole coq tutorial. It's still up there on "Learn X in Y". I forget about this one. I think I wrote it on the train to work over a couple days.
- Applying computational polynomial techniques to optics problems is still a fun thing to consider. <https://www.philipzucker.com/grobner-bases-and-optics/> <https://www.philipzucker.com/ray-tracing-algebraic-surfaces/> . I was in a bit of a commutative algebra phase, learning about grobner bases and sum of squares techniques <https://www.philipzucker.com/computing-syzygy-modules-in-sympy/> <https://www.philipzucker.com/sum-of-squares-optimization-for-minimax-optimal-differential-eq-residuals/> <https://www.philipzucker.com/fiddling-around-with-validated-ode-integration-sum-of-squares-taylor-models/> <https://www.philipzucker.com/deriving-the-chebyshev-polynomials-using-sum-of-squares-optimization-with-sympy-and-cvxpy/>
- Here I'm preparing my Z3 tutorial for FMIE <https://fmie.github.io/agenda.html> which because of Covid was delayed by a year. <https://www.philipzucker.com/programming-and-interactive-proving-with-z3py/>  <https://www.philipzucker.com/stupid-z3py-tricks-verifying-sorting-networks-off-of-wikipedia/> <https://www.philipzucker.com/stupid-z3py-tricks-strikes-back-verifying-a-keras-neural-network/>
- I also started a Julia phase in 2020. Did some minikanren <https://www.philipzucker.com/yet-another-microkanren-in-julia/> , some interesting little computations  <https://www.philipzucker.com/walk-on-spheres-method-in-julia/> and it basically ended when I started writing an Egraph library in Julia <https://www.philipzucker.com/egraph-1/> . Ultimately, my enthusiasm for Julia died because things got stressful in how the egraph thing started panning out. Which is shocking considering how low the stakes were. I think I made the right call in moving on at the time, but maybe there is still some room for Julia in my future. It is a remarkable community in many ways.
- For Catlab.jl, I decided I wanted to try and figure out how to do automated theorem proving for it. Again, the seeds in some ways of what becamne knuckeldragger. <https://www.philipzucker.com/notes-on-synthesis-and-equation-proving-for-catlab-jl/> <https://www.philipzucker.com/theorem-proving-for-catlab-2-lets-try-z3-this-time-nope/> A lot of learning about whaty can and can't be done. This led me to egraphs because i needed an equational reasoning system I could control and understand the guts of. I think that egraphs/equality saturation can be seen as about _partial_ functiosn is kind of a key point here.
- <https://blog.benwiener.com/electronics/projects/programming/2020/11/20/raas.html> I don't think I ever wrote a published post on this. Never not write posts.

## 2021

So began my egraph and datalog era.

- <https://www.philipzucker.com/translating-z3-to-coq/>  This was an interesting exercise. We actually gave our FMIE tutorials <https://www.philipzucker.com/z3-talk-notes/> <https://www.youtube.com/watch?v=56IIrBZy9Rc> 10K views!!! I did a pretty good job here I think. Another lesson in it's better to do things while they are new, or while you are closer to the students on the learning ladder. I think I would do a worse job now because I have a more avdanced understanding and more nuanced interests. n-queens bores the shit out of me.
- Egglog was born! <https://www.philipzucker.com/egglog-checkpoint/> <https://www.philipzucker.com/egglog2-monic/> <https://www.philipzucker.com/egglog-3/>
- Datalog  <https://www.philipzucker.com/notes/Languages/datalog/> I was going nuts on this notes page. I can't believe I wrote so much. <https://www.philipzucker.com/imatch-datalog/> I liked this basic idea that datalog / sql queries are nice way to solve graph matching problems. Again, trivial in some sense once you're more aware of the field of database theory.
- <https://www.philipzucker.com/z3_diff/> This is still basically my plan to deal with differentiation in z3. There is "yoneda" like trick where you can avoid dealing with lambdas. Define your functions like `sin : R -> R` to be partially applied with composition `(sin .) : (R -> R) -> R -> R` and define `X = id : R -> R`. Then you bake in the chain rule into your definition of each constant.
- <https://www.philipzucker.com/z3-cegar-interval/> There is still a fascination with how to hook numerical stuff into z3 from the outside.
- <https://www.philipzucker.com/aesthetic-javascript-eduction/> It's good to make interactive visual stuff. A failure in some respects
- <https://www.philipzucker.com/the-empathy-machine/> The empathy machine was a cool project. Not sure why it didn't get more appreciation. It's dumb in some ways.
- <https://www.philipzucker.com/replacing-rise4fun/> Figured out how to replicated rise4-fun using wasm when it went down. I think this is good exposure for me and I think I helped out z3 and the world a little by getting this working, so a win-win.
- <https://www.philipzucker.com/cars-5/> Cars 5. The legend.
- <https://www.philipzucker.com/marble-machine-progress/> <https://blog.benwiener.com/electronics/projects/programming/2022/02/04/marble-mirror-update.html> Marble machine. What a boondoggle. We took like 2 years fiddling with this. I was kind of miserable for a lot of it. I don't have that kind of staying power.

## 2022

- 2022 started collaborating with the UW folk. I think my blogging output decreased a bit as this was a mental energy outlet and I wasn't comfortable posting things publicly they might feel were derived from private conversations. No one ever indicated this to be the case and I think this was a mistake on my part. It's surprising how powerful slight, even imagined dissuading can stop things from happening.
- <https://www.philipzucker.com/dwarf-patching/>
- A white whale I was chasing was increased datalog expressivity. I currently feel this road leads down to just building an ATP. Resolution.
- <https://www.philipzucker.com/snakelog-post/> Snakelog. A good idea I think if you're a datalog proponent. Just use SQLite / duckdb. So powerful. Embed into python like the z3 bindings. Very powerful.
- The fifty year beep <https://www.philipzucker.com/thousand-year-beep/> Choice shit 👌. Just heard it again last night actually.

## 2023

Yikes late 2022 - early 2023. Tough year.

I think I was driven into complete burnout by the end of 2022 / 2023 and you can see my posting really decreased. At work I had found myself in a role I didn't want, stressed about giving seemingly constant talks about work coworkers were doing and I wasn't sure I believed in. My personal life also had issues. I don't know what I should have done, but I shouldn't have ever let myself be driven that far into the dark. Nothing is worth that. There are too many sunny days, forests and oceans. I'm basically all better now, but it took a while (6 months - a year) even after stepping down.

On a happier note, I was getting into term rewriting. <https://www.philipzucker.com/egraph-ground-rewrite/> The relationship of egraphs to completion is close to trivial from the perspective of someone who knows completion. I didn't know completion. And maybe close to trivial isn't actually trivial. The appeal of egraphs is that you don't have to read a dense book on term rewriting theory to get the gist enough to use or build one.

I remember going on an answer set programming binge during christmas break 2022. That was kind of neat.

I was also putting more into my notes <https://www.philipzucker.com/notes/> section which was an experiment. Eventually it got too unwieldy and I abandoned it to go back to a more temporal (in terms of when I was thinking about it) organization rather than rolling release and global organization by topic.

## 2024

Here I did a blog post a week as my new years resolution. I already just retrospected this here <https://www.philipzucker.com/2024_year/>

# Hi Future Me

Congrats to me! Well done, Phil! Keep it up! Be proud of the things you've done, big and small. Your fuckups weren't that bad. Live well and happy. Stop if it's not fun or you need room for new things. It's all good, baby.
