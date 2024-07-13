---
title: Youtube
layout: post
---

Go to google takeout. Deselect. go down to youtube at the bottom.
Change the exports to subscriptions/playlists/channels
Hmm. Way too clunk.
The playlistso nly have vid id. Not good enough. Could write script I guess.

<https://www.reddit.com/r/DataHoarder/wiki/index/>

<https://www.reddit.com/r/DataHoarder/comments/dxn6fx/is_there_any_way_to_export_a_youtube_playlist/>

youtube-dl is the way to go I guess

`youtube-dl --flat-playlist --dump-json https://www.youtube.com/playlist?list=PLqggUNm8QSqldCY-MrUktblGeaQOVRt2L > prog10.json`

<https://github.com/yt-dlp> hmm this is better?

chatgpt made this script for extraction

```python
import json
import glob
import os

# Path to the directory containing your JSON files
JSON_DIR_PATH = './'
MARKDOWN_FILE_PATH = './all_playlists.md'

def load_playlists(json_dir_path):
    """
    Load playlists data from all JSON files in the specified directory.
    """
    playlists = {}
    json_files = glob.glob(os.path.join(json_dir_path, '*.json'))
    
    for file_path in json_files:
        with open(file_path, 'r') as file:
            filename = os.path.basename(file_path)
            playlists[filename] = []
            for line in file:
                try:
                    playlists[filename].append(json.loads(line))
                except json.JSONDecodeError as e:
                    print(f"Error decoding JSON from file {file_path}: {e}")
    return playlists

def playlists_to_markdown(playlists):
    """
    Convert a list of playlists to a markdown string.
    """
    markdown_str = "# YouTube Playlists\n\n"
    for filename, videos in playlists.items():
        markdown_str += f"## {filename}\n\n"
        for video in videos:
            title = video.get('title', 'No title available')
            video_id = video.get('id', 'No ID available')
            url = f"https://www.youtube.com/watch?v={video_id}" if video_id != 'No ID available' else 'No URL available'

            markdown_str += f"### [{title}]({url})\n\n"
        markdown_str += "---\n\n"
    return markdown_str

def save_to_file(content, filename):
    """
    Save a string to a markdown file.
    """
    with open(filename, 'w') as file:
        file.write(content)

if __name__ == "__main__":
    playlists = load_playlists(JSON_DIR_PATH)
    markdown_content = playlists_to_markdown(playlists)
    save_to_file(markdown_content, MARKDOWN_FILE_PATH)
    print(f"All playlists saved to {MARKDOWN_FILE_PATH}")


```

# YouTube Playlists

## prog3.json

### [Multi-Party Computation: From Theory to Practice](https://www.youtube.com/watch?v=pNNLAEygPQI)

### [Introduction to Grobner Bases - Prof. Bernd Sturmfels](https://www.youtube.com/watch?v=TNO5WuxuNak)

### [Nonlinear algebra, Lecture 1: "Polynomials, Ideals, and Groebner Bases", by Bernd Sturmfels](https://www.youtube.com/watch?v=1EryuvBLY80)

### [Marta Kwiatkowska, "Probabilistic model checking of labelled Markov processes"](https://www.youtube.com/watch?v=SONj64dXjUo)

### [Matrix-free Construction of HSS Representations Using Adaptive Randomized Sampling](https://www.youtube.com/watch?v=c8sEvAIeqjM)

### [Randomized Numerical Linear Algebra: Overview](https://www.youtube.com/watch?v=xlFRURt0nss)

### [Randomized Algorithms for Computing Full Matrix Factorizations](https://www.youtube.com/watch?v=882BKbiuZng)

### [The Fast Multipole Method](https://www.youtube.com/watch?v=qMLIyZi8Sz0)

### [ICFP 2018 Keynote Address: Gradual Typing](https://www.youtube.com/watch?v=fQRRxaWsuxI)

### [Relational Algebra by Way of Adjunctions](https://www.youtube.com/watch?v=4g86dRKiVyU)

### [ICFP 2018 Keynote Address: The Role of Functional Programming and DSLs in Hardware](https://www.youtube.com/watch?v=VqYkcGRr8x0)

### [Fault Tolerant Functional Reactive Programming](https://www.youtube.com/watch?v=owojLkI5YyY)

### [Ready, Set, Verify! Applying hs-to-coq to Real-World Haskell Code](https://www.youtube.com/watch?v=9QL97E0cNk0)

### [Teaching How to Program using Automated Assessment and Functional Glossy Games](https://www.youtube.com/watch?v=cRtoMWEGo90)

### [Static Interpretation of Higher-Order Modules in Futhark - Functional GPU Programming in the Large](https://www.youtube.com/watch?v=V6OTt1EiZHw)

### [What's the Difference? A Functional Pearl on Subtracting Bijections](https://www.youtube.com/watch?v=hq9gAe-pmzM)

### [ICFP 2018 Keynote Address: Conveying the Power of Abstraction](https://www.youtube.com/watch?v=PvSpyhm6TUU)

### [ELAGB - Brice Boyer: LinBox : 15 years](https://www.youtube.com/watch?v=nQysRFKyCFw)

### [ELAGB - Martin Albrecht: The M4RI and M4RIE libraries](https://www.youtube.com/watch?v=PjDVn6dOh5k)

### [Factorizing Finite Automata: The Holonomy Decomposition](https://www.youtube.com/watch?v=J2GpOUIAW04)

### [ETAPS 2016 - K: a semantic framework for programming languages and formal analysis tools - G. Rosu](https://www.youtube.com/watch?v=3ovulLNCEQc)

### [SPIN 2016 - Model Checking: What Have We Learned, What Will Machines Learn? - Pierre Wolper](https://www.youtube.com/watch?v=yWSNSmtuHCs)

### [Integer Programming in Polynomial Time, Shmuel Onn, Osaka Japan](https://www.youtube.com/watch?v=WvA2Yap_aWM)

### [DAY3 2 15: Invited tutorial (Shmuel Onn)](https://www.youtube.com/watch?v=dXH1QBgSoTo)

### [Advances in Numerical Algebraic Geometry with Applications](https://www.youtube.com/watch?v=80Z2dw9GYtA)

### [Chordal Structure and Polynomial Systems](https://www.youtube.com/watch?v=6du4K4Gl9sk)

### [Recent Progress on Computing Groebner Bases](https://www.youtube.com/watch?v=PqoyfxBV0OI)

### [Numerical Algebraic Geometry](https://www.youtube.com/watch?v=eK3sIjboaxA)

### [Introduction to Tropical Algebraic Geometry (1 of 5)](https://www.youtube.com/watch?v=unjVp6HQVmc)

### [Maxim Kontsevich: What is tropical mathematics? [2013]](https://www.youtube.com/watch?v=DV-8kEn8udY)

### [Bernd Sturmfels (University of California, Berkeley) / Lecture 1 : Elementary Introduction](https://www.youtube.com/watch?v=_u6TU-oGNr4)

### [Bernd Sturmfels (UC Berkeley) / Introduction to Non-Linear Algebra : Tropical Algebra I / 2014-06-05](https://www.youtube.com/watch?v=9nIXNcK3WI4)

### [Nonlinear algebra, Lecture 3: "Elimination and Implicitization", by Bernd Sturmfels](https://www.youtube.com/watch?v=cv14Y_6AvVM)

### [Norbert Schuch: Matrix product states and tensor networks (I)](https://www.youtube.com/watch?v=W_IBEAzqm4U)

### [Tips and Tricks for Optimal Scheduling with End-to-End Analytics and Gurobi](https://www.youtube.com/watch?v=0EUX3ua2liU)

### [Macaulay 2 Tutorial I](https://www.youtube.com/watch?v=i9cTeVp8jeo)

### [Nonlinear algebra, Lecture 6: "Tropical Algebra", by Bernd Sturmfels](https://www.youtube.com/watch?v=lvIRYQYfu-M)

### [On Optimal Algorithms and Assumption Factories](https://www.youtube.com/watch?v=I7o5rhVvAGI)

### [Multiparty Computation Research](https://www.youtube.com/watch?v=bSC4rCHbLlc)

### [Nonlinear algebra, Lecture 7: "Toric Varieties", by Mateusz Michalek](https://www.youtube.com/watch?v=5EQnMHf_i-Q)

### ["Your Secrets are Safe with Julia: A Compiler for Secure Computation" by Jason Dagit](https://www.youtube.com/watch?v=-vxkri3o3mA)

### [Great Ideas in Theoretical Computer Science: Epilogue: Why Max-Cut is My Favorite (Spring 2015)](https://www.youtube.com/watch?v=3sZOa17Uqms)

### [Analysis of Boolean Functions at CMU - Lecture 1: The Fourier expansion and basic formulas](https://www.youtube.com/watch?v=JIruJ8edYYM)

### [Spring 2015 Lecture 16   Godel's Incompleteness Theorems default](https://www.youtube.com/watch?v=aMHPi9GcSXw)

### [Analysis of Boolean Functions. Part I | Ryan O'Donnell | Лекториум](https://www.youtube.com/watch?v=DebrwgWmToc)

### ["Hackett: a metaprogrammable Haskell" by Alexis King](https://www.youtube.com/watch?v=5QQdI3P7MdY)

### [ECE 804 - Fall 2011 - Lecture 001 with Dr. Seth Sullivant - Aug. 26, 2011](https://www.youtube.com/watch?v=KJNi3LDVWVI)

### [Prof. Dr. Eva Riccomagno - Algebraic Statistics I (SEAMS SCHOOL)](https://www.youtube.com/watch?v=pB5cxpTY36Y)

### [Bernd Sturmfels (Univ. of California at Berkeley) / An Invitation to Algebraic Statistics](https://www.youtube.com/watch?v=XVmZFn3EPXU)

### [Stanford Lecture: Donald Knuth - "Trees and chordal graphs" (2012)](https://www.youtube.com/watch?v=txaGsawljjA)

---

## programming.json

### [Introduction to Type Inference](https://www.youtube.com/watch?v=il3gD7XMdmA)

### [Phil Freeman - Embedded DSLs in Haskell](https://www.youtube.com/watch?v=8DdyWgRYEeI)

### [Marta Kwiatkowska, "Probabilistic model checking of labelled Markov processes"](https://www.youtube.com/watch?v=SONj64dXjUo)

### [Rustan Leino, Microsoft Research - Program Verification: Yesterday, Today, Tomorrow](https://www.youtube.com/watch?v=5t4WntcsZZo)

### [​Proof Theory of Homotopy Type Theories by Ulrik Buchholtz (Carnegie Mellon University, USA)](https://www.youtube.com/watch?v=ZQyBLXJQs2w)

### [Lecture 1 | A survey of automated theorem proving | John Harrison | Лекториум](https://www.youtube.com/watch?v=Nydg-N83VYc)

### [Olivia Caramello - 1/4 Introduction to categorical logic, classifying toposes...](https://www.youtube.com/watch?v=KtNlItQOE9E)

### [Efficiently coding for modern CPUs by Edward Kmett](https://www.youtube.com/watch?v=KzqNQMpRbac)

### [Functional Programmers Paris - Building a language, in Haskell, with an LLVM backend](https://www.youtube.com/watch?v=I51TRpl1qic)

### [Bartosz Milewski - Arrows are strong profunctors](https://www.youtube.com/watch?v=hrNfkP8iKAs)

### [John Leo: Dependent Types in GHC](https://www.youtube.com/watch?v=buVyfrU6QF4)

### [Phil Freeman - PureScript's Typesystem](https://www.youtube.com/watch?v=SPpIbiZFPRY)

### [Edward Kmett - Type Classes vs. the World](https://www.youtube.com/watch?v=hIZxTQP1ifo)

### [Backpack to Work: Towards Backpack in Practice](https://www.youtube.com/watch?v=A3ehG4GQpxU)

### [Gershom Bazerman on "Homological Computations for Term Rewriting Systems" [PWL NYC]](https://www.youtube.com/watch?v=WdawrT-6Qzk)

### [LambdaConf 2015 - The Art of Program Derivation and Parallel Computation Gershom Bazerman](https://www.youtube.com/watch?v=JDqD6RZpnZA)

### [Simon Peyton Jones on Getting from A to B fast route finding on slow computers [PWL London]](https://www.youtube.com/watch?v=L1XDdy-hOH8)

### [A Categorical View of Computational Effects](https://www.youtube.com/watch?v=6t6bsWVOIzs)

### [Lecture 1 — Distributed File Systems | Stanford University](https://www.youtube.com/watch?v=xoA5v9AO7S0)

### [Solving QBF by Counterexample-Guided Abstraction Refinement](https://www.youtube.com/watch?v=i2CQDEI05W8)

### [ICAPS 2017: Tutorial : AI Planning for Robotics and Human-Robot Interaction](https://www.youtube.com/watch?v=F9wymWzSND8)

### [ICAPS 2017: Tutorial : Knowledge Engineering in Planning: Representation Matters](https://www.youtube.com/watch?v=gUwn55Gkd9U)

### [ICAPS 2014 Invited Talk: Peter Wurman](https://www.youtube.com/watch?v=YSrnV0wZywU)

### [Revisiting Combinators by Edward Kmett](https://www.youtube.com/watch?v=PA1Fc7DNKtA)

### [CVPR18: Tutorial: Part 1: Generative Adversarial Networks](https://www.youtube.com/watch?v=EXLRZr0k8ok)

### [ICAPS 2016: ROSPlan Tutorial](https://www.youtube.com/watch?v=I7BPKMTYcD8)

### [Functional DevOps in a Dysfunctional World](https://www.youtube.com/watch?v=RsSNEkBGmj0)

### [Code Generation with llvm-hs by Stephen Diehl](https://www.youtube.com/watch?v=wn-xW3g8jXY)

### [ZuriHac 2015 - Performance](https://www.youtube.com/watch?v=_pDUq0nNjhI)

### [CVPR18:Tutorial: Inverse Reinforcement Learning for Computer Vision](https://www.youtube.com/watch?v=JbNeLiNnvII)

### [ICAPS 2014: Tutorial on Constraint-Based Temporal Reasoning  (Part 1)](https://www.youtube.com/watch?v=NOtSLqIawk8)

### [Alexey Kuleshevich: massiv - Haskell arrays that are easy and fast](https://www.youtube.com/watch?v=AAx2a0bUsxA)

### [Category Theory III 2.1: String Diagrams part 1](https://www.youtube.com/watch?v=eOdBTqY3-Og)

### [Category Theory III 2.2, String Diagrams part 2](https://www.youtube.com/watch?v=lqq9IFSPp7Q)

### [Spatial: A Language and Compiler for Application Accelerators](https://www.youtube.com/watch?v=A94ChZ8Kv34)

### [Julia for Robotics: RigidBodyDynamics.jl and Related Tools](https://www.youtube.com/watch?v=SkA4Ih-R3mc)

### [JuMP-dev 2018 | Developing new optimization methods with JuliaSmoothOptimizers | Abel Siqueira](https://www.youtube.com/watch?v=-iGk5LlMr-Q)

### [JuMP-dev 2018 | Systematically building MIP formulations using JuMP and Julia | Joey Huchette](https://www.youtube.com/watch?v=j-v48n1VVeg)

### [RI Seminar: Michael Kaess : Robust and Efficient Real-time Mapping for Autonomous Robots](https://www.youtube.com/watch?v=_W3Ua1Yg2fk)

### [Category Theory III 3.1, Adjunctions and monads](https://www.youtube.com/watch?v=9p6_U5yV0ro)

### [Factor Graphs for Flexible Inference in Robotics and Vision | Frank Dellaert | Robotics@MIT](https://www.youtube.com/watch?v=hCxiAkOu07c)

### [Keynote: Tricks and Tips in Numerical Computing | Nick Higham | JuliaCon 2018](https://www.youtube.com/watch?v=Q9OLOqEhc64)

### [Hierarchical Tensor Decompositions in Julia | Frank Otto | JuliaCon 2018](https://www.youtube.com/watch?v=8QGo98705jY)

### [Solving Partial Differential Equations With Julia | Chris Rackauckas | JuliaCon 2018](https://www.youtube.com/watch?v=okGybBmihOE)

### [A practical introduction to metaprogramming in Julia | Andy Ferris | JuliaCon 2018](https://www.youtube.com/watch?v=SeqAQHKLNj4)

### [JuliaRobotics: Making robots walk with Julia | Robin Deits](https://www.youtube.com/watch?v=dmWQtI3DFFo)

### [Numerical Analysis in Julia | Sheehan Olver | JuliaCon 2018](https://www.youtube.com/watch?v=MAhLlLOxWGg)

### [Natural Language Processing workshop using Julia | Avik Sengupta | JuliaCon 2018](https://www.youtube.com/watch?v=f7RNuOLDyM8)

### [An Introduction to High Performance Custom Arrays | Matt Bauman | JuliaCon 2018](https://www.youtube.com/watch?v=jS9eouMJf_Y)

### [Symbolic Mathematics in Julia | John Lapyre | JuliaCon 2018](https://www.youtube.com/watch?v=M742_73edLA)

### [Sum-of-squares optimization in Julia (Benoît Legat, Université Catholique de Louvain)](https://www.youtube.com/watch?v=kyo72yWYr54)

### [LP/SDP Hierarchies and Sum of Squares Proofs 1](https://www.youtube.com/watch?v=HdZajqWl15I)

### [Challenges in Adiabatic Optimization](https://www.youtube.com/watch?v=pmz3hQUTnjQ)

---

## prog9.json

### [George Wilson  - An Intuition for Propagators  - Compose Melbourne 2019](https://www.youtube.com/watch?v=nY1BCv3xn24)

### [Logic, Co-induction and Infinite Computation](https://www.youtube.com/watch?v=nOqO5OlC920)

### [Brendan Zabarauskas  - Lost in a Universe of Types - Compose Melbourne 2019](https://www.youtube.com/watch?v=L9TubiWkBZ8)

### [2019 ADSI Summer Workshop: Algorithmic Foundations of Learning and Control, Ben Recht](https://www.youtube.com/watch?v=wsjQSMMFJbM)

### [Phebe Vayanos, Robust Optimization & Sequential Decision-Making](https://www.youtube.com/watch?v=clzfqPgLb1A)

### [MBSE Colloquium: Sasa Rakovic, "Robust Model Predictive Control"](https://www.youtube.com/watch?v=iVjuzfP3Jk0)

### [Pragmatic Algorithmic Game Theory](https://www.youtube.com/watch?v=ylJ5yUudsB0)

### [On Algorithmic Game Theory I](https://www.youtube.com/watch?v=ggi2PZbO0oQ)

### [LSE Events | Tim Roughgarden | Game Theory Through the Computational Lens](https://www.youtube.com/watch?v=7HYJ2oJtLZk)

### [Approximation Algorithms for Optimization under Uncertainty](https://www.youtube.com/watch?v=yTvNMeTcK4c)

### [Michael Arntzenius - DB ⋈ FP = Datafun: a new functional query language](https://www.youtube.com/watch?v=7HUotKIVFig)

### [MPC and MHE implementation in Matlab using Casadi | Part 1](https://www.youtube.com/watch?v=RrnkPrcpyEA)

### [JuMP-dev 2019 | Marcelo Forets | Reachset Approximation with JuMP](https://www.youtube.com/watch?v=Pd5Yq16BMOE)

### [David I. Spivak - A topos-theoretic approach to systems and behavior (joint work with P. Schultz)](https://www.youtube.com/watch?v=lPxc4j7yNIU)

### [Correctness proofs of distributed systems with Isabelle/HOL](https://www.youtube.com/watch?v=Uav5jWHNghY)

---

## prog7.json

### [Leslie Lamport, 2013  ACM Turing Award Recipient - Part 1](https://www.youtube.com/watch?v=JhexdgiFWfA)

### [Niklaus Wirth, 1984 ACM Turing Award Recipient](https://www.youtube.com/watch?v=SUgrS_KbSI8)

### [Lamport TLA+ Course Lecture 6: Two-Phase Commit (HD)](https://www.youtube.com/watch?v=U4mlGqXjtoA)

### [Lamport TLA+ Course Lecture 7: Paxos Commit  (HD)](https://www.youtube.com/watch?v=u7fTLyiSnZw)

### [Lamport TLA+ Course Lecture 5: Transaction Commit (HD)](https://www.youtube.com/watch?v=JwO4yPSEp-0)

### [Lattices: Algorithms, Complexity, and Cryptography](https://www.youtube.com/watch?v=GOQkjFdSG94)

### [A Practical Construction for Decomposing Numerical Abstract Domains](https://www.youtube.com/watch?v=t_ht1p67tOA)

### [Fast Polyhedra Abstract Domain](https://www.youtube.com/watch?v=SdOaoIcVZAY)

### [Jörgen Brandt - Beyond state machines: services as petri nets - Code BEAM STO](https://www.youtube.com/watch?v=aWnGPaputGE)

### [John Valois on Wait-Free Synchronization [PWL NYC]](https://www.youtube.com/watch?v=7end3rQ0jkk)

### ["Datafun: a functional query language" by Michael Arntzenius](https://www.youtube.com/watch?v=gC295d3V9gE)

### [Papers We Love San Diego - An Axiomatic Basis for Computer Programming](https://www.youtube.com/watch?v=K1oj7k_41Ws)

### ["Papers I Have Loved" by Casey Muratori](https://www.youtube.com/watch?v=SDS5gLSiLg0)

### [Michael Bernstein on A Uniﬁed Theory of Garbage Collection](https://www.youtube.com/watch?v=XtUtfARSIv8)

### ["A Rehabilitation of Message-passing Concurrency" by Frank Pfenning [PWLConf 2018]](https://www.youtube.com/watch?v=LRn_nPfti-Y)

### [Jean Yang on An Axiomatic Basis for Computer Programming](https://www.youtube.com/watch?v=GQi-6-d5ooQ)

### [What type of thing is a type? by Ron Garcia](https://www.youtube.com/watch?v=jVyz3lWH2bA)

### [PWLTO#11 – Peter Sobot on An Industrial-Strength Audio Search Algorithm](https://www.youtube.com/watch?v=WhXgpkQ8E-Q)

### [Logical Analysis of Hybrid Systems](https://www.youtube.com/watch?v=bSdoLm8ZmSc)

### [Feedback Control of Hybrid Dynamical Systems](https://www.youtube.com/watch?v=08JJFK9lhQk)

### [Real-Time Decision Making in Hybrid Systems](https://www.youtube.com/watch?v=6y-dWHChVxw)

### [Real-Time Convex Optimization](https://www.youtube.com/watch?v=uhGMnT12zOg)

### [Core-sets for Real-Time Tracking using Caratheodory Theorem, with Applications to Drones](https://www.youtube.com/watch?v=DaykAgmvSfI)

### ["Everything Old is New Again: Quoted Domain Specific Languages" by Philip Wadler](https://www.youtube.com/watch?v=DlBwJ4rvz5c)

### [Máté Karácsony: Zeldspar - The Road to Epiphany](https://www.youtube.com/watch?v=GY5SxLkVyp4)

### [Tech Mesh 2012 - Making EDSLs fly - Lennart Augustsson](https://www.youtube.com/watch?v=7gF7iFB4mFY)

### [Stanford Seminar - Concatenative Programming: From Ivory to Metal](https://www.youtube.com/watch?v=_IgqJr8jG8M)

### [Vitaly Bragilevsky - Type Theory Behind Glasgow Haskell Compiler Internals (Part 1) - λC 2018](https://www.youtube.com/watch?v=2bPRvmoIGi0)

### [Timed transition systems](https://www.youtube.com/watch?v=tUSxi_rSXwo)

### [Lecture 20 | MIT 6.832  (Underactuated Robotics), Spring 2019](https://www.youtube.com/watch?v=bw71ElvpokE)

### [Lecture 22 | MIT 6.832 (Underactuated Robotics), Spring 2019](https://www.youtube.com/watch?v=FZ6C0sDnVSU)

### [Lecture 23 | MIT 6.832 (Underactuated Robotics), Spring 2019](https://www.youtube.com/watch?v=tWyqEZhyZZQ)

---

## prog6.json

### [Xing Gao 9/11/15 Part 1](https://www.youtube.com/watch?v=GnYwWvuOxgA)

### [Quantum Approximate Optimization Algorithms (Peter Shor, ISCA 2018)](https://www.youtube.com/watch?v=HHIWUi3GmdM)

### [Daniel Lidar - "Adventures in Quantum Optimization" (UMBC Colloquium 2018)](https://www.youtube.com/watch?v=OL04fJsMoe8)

### [Language, Compiler, and Optimization Issues in Quantum Computing - Margaret Martonosi - June 10 2015](https://www.youtube.com/watch?v=laDOWsrx_VM)

### [Game Semantics [1/4] - Dan R. Ghica - OPLSS 2018](https://www.youtube.com/watch?v=EpGGenaS-mQ)

### [Nonlinear algebra, Lecture 11: "Semidefinite Programming", by Bernd Sturmfels](https://www.youtube.com/watch?v=of4v2Y0Cun0)

### [Nonlinear algebra, Lecture 12: "Primary Decomposition ", by Mateusz Michalek and Bernd Sturmfels](https://www.youtube.com/watch?v=E8G0p7MbiG8)

### [Nonlinear algebra, Lecture 13: "Polytopes and Matroids ", by Mateusz Michalek](https://www.youtube.com/watch?v=__LtBBXUPtk)

### [Hyperbolic Optimization, Part I - A](https://www.youtube.com/watch?v=-adBdluVXWU)

### [Practical Boogie (on the example of VCC)](https://www.youtube.com/watch?v=SzjQFbzDE3I)

### [ACT@UCR Seminar: Systems as Wiring Diagram Algebras - Christina Vasilakopoulou](https://www.youtube.com/watch?v=dEDtaJhgQOY)

### [Statistical Inference and Privacy, Part I](https://www.youtube.com/watch?v=_nQSqsHRteo)

### [Jules Hedges: Compositional Game Theory](https://www.youtube.com/watch?v=C64905vTT3s)

### [Daniel Spielman “Miracles of Algebraic Graph Theory”](https://www.youtube.com/watch?v=CDMQR422LGM)

### [Jesús A. De Loera, "Algebraic, Geometric, and Topological Methods in Optimization"](https://www.youtube.com/watch?v=4hAI-SSTlV4)

### [Benedict Gross “Complex Multiplication: Past, Present, Future” Lecture 1](https://www.youtube.com/watch?v=ZtBX13C5N04)

### [Bryna Kra “Dynamics of Systems with Low Complexity”](https://www.youtube.com/watch?v=cXl0GsQzs9k)

### [Peter Ozsvath “From Knots to Symplectic Geometry and Algebra”](https://www.youtube.com/watch?v=RArAHA3Oe7M)

### [Graph Sparsification I: Sparsification via Effective Resistances](https://www.youtube.com/watch?v=qXRs8-LouSQ)

### [Spectral Graph Theory I: Introduction to Spectral Graph Theory](https://www.youtube.com/watch?v=01AqmIU9Su4)

### [The Unreasonable Effectiveness of Spectral Graph Theory: A Confluence of Algorithms, Geometry & ...](https://www.youtube.com/watch?v=8XJes6XFjxM)

### [High Performance Haskell by Harendra Kumar at #FnConf18](https://www.youtube.com/watch?v=aJvwORrBJ0o)

### [The Mathematics of Networks](https://www.youtube.com/watch?v=IyJP_7ucwWo)

### [ACT2018: Dan Ghica — Diagrammatic semantics for digital circuits](https://www.youtube.com/watch?v=Lo7Bg8OsDII)

### [ORC IAP Seminar 2019 - Bartolomeo Stellato](https://www.youtube.com/watch?v=NbE5huZS-wU)

### [The Geometry of Matroids](https://www.youtube.com/watch?v=FKTPFy-MGp0)

### [Constraints Liberate, Liberties Constrain — Runar Bjarnason](https://www.youtube.com/watch?v=GqmsQeSzMdw)

### [MuniHac 2018: Keynote: Beautiful Template Haskell](https://www.youtube.com/watch?v=AzJVFkm42zM)

### [Rayon: Data Parallelism for Fun and Profit — Nicholas Matsakis](https://www.youtube.com/watch?v=gof_OEv71Aw)

### [LambdaConf 2015 - Finally Tagless DSLs and MTL   Joseph Abrahamson](https://www.youtube.com/watch?v=JxC1ExlLjgw)

### [Phil Freeman - Embedded DSLs in Haskell](https://www.youtube.com/watch?v=8DdyWgRYEeI)

### [Bryan O'Sullivan/ Facebook- Fast Code Nation: The Bright Side of High Level Languages](https://www.youtube.com/watch?v=kGa78HQv_LQ)

### [MuniHac 2018: Keynote: A low-latency garbage collector for GHC](https://www.youtube.com/watch?v=7_ig6r2C-d4)

### [MuniHac 2018: Keynote: The Curious Case of Pattern-Match Coverage Checking](https://www.youtube.com/watch?v=nDmNTRG1V_0)

### [Haskell Live-Coding, Session 8, Succinct Data Structures and Dynamization](https://www.youtube.com/watch?v=9MKEmNNJgFc)

### [Rohit Grover - Prototype Driven Development using Haskell - Compose Melbourne 2018](https://www.youtube.com/watch?v=2AwLd-CTgrU)

### [Tim McGilchrist - Dependently Typed State Machines - Compose Melbourne 2018](https://www.youtube.com/watch?v=AgRmpMPCKeU)

### [HaskellerZ - May 2018 - Andreas Herrmann - GHC Hacking Newcomer Guide](https://www.youtube.com/watch?v=s9DkByHSdOg)

### [HaskellerZ - January 2019 - Michal Terepeta - Implementing Immutable Vectors in Haskell](https://www.youtube.com/watch?v=fV9ZQecPbmc)

### [TUTORIAL: In-memory Representations of Databases via Succinct Data Structures](https://www.youtube.com/watch?v=_3q7T_5JaTI)

### [Konstantin Ignatov - Succinct data structures for python](https://www.youtube.com/watch?v=EVP_xLILirs)

### [Haskell 2014: Reflection without Remorse: Revealing a hidden sequence to speed up monadic reflection](https://www.youtube.com/watch?v=_XoI65Rxmss)

### [2018 09 27 - Simon Meier - Test-Driven Development of a Unification Algorithm](https://www.youtube.com/watch?v=NWu1ln-YiY4)

### [David Spivak: Categorical Databases](https://www.youtube.com/watch?v=bk36__qkhrk)

### [Gurobi Webinar: The Grain Drain: Large-Scale Grain Port Terminal Optimization with Biarri](https://www.youtube.com/watch?v=TB56nrUWVKg)

### [Rust Async Programming in 2018 • Katharina Fey • GOTO 2018](https://www.youtube.com/watch?v=j0SIcN-Y-LA)

### [Niko Matsakis - Rust: Putting Ownership to Use](https://www.youtube.com/watch?v=wXoY91w4Agk)

### [Rust Cologne:  The Cost of Zero Cost](https://www.youtube.com/watch?v=JlVWk_fbvzI)

### [A Modular Integration of SAT/SMT Solvers to Coq through Proof Witnesses](https://www.youtube.com/watch?v=Zrho5lDJ67o)

### [Network Analysis. Lecture 1. Introduction to Network Science](https://www.youtube.com/watch?v=UHnmPu8Zevg)

### [Network Analysis. Lecture 9. Graph partitioning algorithms](https://www.youtube.com/watch?v=4jGcDq_ZFoA)

### [High-performance Tree Wrangling, the APL Way // Aaron Hsu // Dyalog '18](https://www.youtube.com/watch?v=hzPd3umu78g)

### [Patterns and Anti-patterns in APL // Aaron Hsu // Dyalog '17](https://www.youtube.com/watch?v=9xCJ3BCIudI)

### [6.875 (Cryptography) L12: Zero Knowledge I](https://www.youtube.com/watch?v=IWF-U1B1KQI)

### [Implementing In-memory Caches in Haskell](https://www.youtube.com/watch?v=Ni2QPZ-VU2k)

### [Array-oriented Functional Programming by Aaron W Hsu, Dhaval Dalal and Morten Kromberg at #FnConf18](https://www.youtube.com/watch?v=Gsj_7tFtODk)

### [Geometric deep learning](https://www.youtube.com/watch?v=wLU4YsC_4NY)

### [Mathieu Tanneau @ JuMP-dev 2019](https://www.youtube.com/watch?v=d0Ua-YWIdug)

### [Michael Garstka @ JuMP-dev 2019](https://www.youtube.com/watch?v=VTxPqEzzqlU)

### [Many-body Physics and Complexity I](https://www.youtube.com/watch?v=KTB-xSOPaZM)

### [Random Matrices: Theory and Practice - Lecture 1](https://www.youtube.com/watch?v=Je4bU3g_QGk)

### ["A (Not So Gentle) Introduction To Systems Programming In ATS" by Aditya Siram](https://www.youtube.com/watch?v=zt0OQb1DBko)

### [Intro to ATS #1 -- good programmers and best programmers](https://www.youtube.com/watch?v=kl7vrWdxTPQ)

### [CppCon 2018: Bjarne Stroustrup “Concepts: The Future of Generic Programming (the future is here)”](https://www.youtube.com/watch?v=HddFGPTAmtU)

### [Cedille Cast #1: Deriving Induction (Pt. 1)](https://www.youtube.com/watch?v=A5c-KVMRSds)

### [Haskell Live-Coding, Session 25, Guanxi Review](https://www.youtube.com/watch?v=ISNYPKiE0YU)

### ["Type-Driven Program Synthesis" by Nadia Polikarpova](https://www.youtube.com/watch?v=HnOix9TFy1A)

### [Constraint Solvers for the Working PL Researcher](https://www.youtube.com/watch?v=AkKOZjYmH74)

### [Program Synthesis meets Machine Learning](https://www.youtube.com/watch?v=Q_Gyca1O1Lw)

### [The Four Big Bets (Illustrated via a Journey in Program Synthesis)](https://www.youtube.com/watch?v=ttboblOwy0g)

### [Program Synthesis for the Masses](https://www.youtube.com/watch?v=NAoSTmCUlW0)

### [Type-Driven Program Synthesis](https://www.youtube.com/watch?v=Q-3tcbUyF34)

### [Abstractions for Expressive, Efficient Parallel and Distributed Computing](https://www.youtube.com/watch?v=4h7YBUXiCZE)

### [Jane and the Compiler](https://www.youtube.com/watch?v=gXdMFxGdako)

### [JuMP-dev 2019 | Benoit Legat | Set Programming with JuMP](https://www.youtube.com/watch?v=hV3G-eNLNjk)

### [JuMP-dev 2019 | David Sanders | Rigorous global optimization in pure Julia](https://www.youtube.com/watch?v=D6BSXD5gMRk)

### [JuMP-dev 2019 | Marcelo Forets | Reachset Approximation with JuMP](https://www.youtube.com/watch?v=Pd5Yq16BMOE)

### [JuMP-dev 2019 | Tillmann Weisser | JuliaMoments](https://www.youtube.com/watch?v=6byXrNX-Frw)

### [How the chalk-engine crate works](https://www.youtube.com/watch?v=Ny2928cGDoM)

### [CMU Advanced Database Systems - 22 Query Optimizer Implementation (Part I) (Spring 2019)](https://www.youtube.com/watch?v=iEyu7AcOhuI)

### [2019 EuroLLVM Developers’ Meeting: I. Wolff “The Helium Haskell compiler and its new LLVM backend”](https://www.youtube.com/watch?v=x6CBks1paF8)

### [CMU Advanced Database Systems - 23 Query Optimizer Implementation (Part 2) (Spring 2019)](https://www.youtube.com/watch?v=BQNsGoZ--Is)

### [CMU Advanced Database Systems - 17 Parallel Hash Join Algorithms (Spring 2019)](https://www.youtube.com/watch?v=vPP1CwCGjVg)

### [BOB 2019 - Joachim Breitner, Inspection Testing](https://www.youtube.com/watch?v=RBB9f5xN_c8)

### [BOB 2019 - Tikhon Jelvis, Analyzing Programs with SMT Solvers](https://www.youtube.com/watch?v=sY0px-LXtGI)

### [Lamport TLA+ Course Lecture 5: Transaction Commit (HD)](https://www.youtube.com/watch?v=JwO4yPSEp-0)

### [Lamport TLA+ Course Lecture 6: Two-Phase Commit (HD)](https://www.youtube.com/watch?v=U4mlGqXjtoA)

---

## feed.json

### ["An Introduction to Combinator Compilers and Graph Reduction Machines" by David Graunke](https://www.youtube.com/watch?v=GawiQQCn3bk)

### [Relational Programming in miniKanren by William Byrd, Part 2/2](https://www.youtube.com/watch?v=nFE2E91VDAk)

### [Charlie Kaufman | BAFTA Screenwriters’ Lecture Series](https://www.youtube.com/watch?v=eRfXcWT_oFs)

### [Monoidal Parsing - Boston Haskell Meetup](https://www.youtube.com/watch?v=090hIEiUoE0)

### [Majorana 'Particle' in Condensed Matter Systems by Sankar Das Sarma](https://www.youtube.com/watch?v=yH-Eqx4ow0k)

### [The simple essence of automatic differentiation](https://www.youtube.com/watch?v=Shl3MtWGu18)

### [Why GHC Core and Linear Logic Should be Best Friends](https://www.youtube.com/watch?v=YaQycMNc9S4)

### ["Controlling Time and Space: understanding the many formulations of FRP" by Evan Czaplicki](https://www.youtube.com/watch?v=Agu6jipKfYw)

### [Chap 2: Hadamard & Picard Conditions, Singular Value Expansion, Naive Reconstruction - 1](https://www.youtube.com/watch?v=XG0OBp-d7zI)

### [The Convex Geometry of Inverse Problems](https://www.youtube.com/watch?v=pcIGP9X9E40)

### [Techniques for combinatorial optimization: Spectral Graph Theory and Semidefinite Programming](https://www.youtube.com/watch?v=ADwygfTLR5g)

### [Lecture 9 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=zgdjU4G1QUE)

### [#2 Cyclone 5 and memory mapping](https://www.youtube.com/watch?v=0XRn5KbnzYA)

### [Lambda Days 2018 - Paweł Szulc - Understanding Distributed Calculi in Haskell](https://www.youtube.com/watch?v=QTPRb9mTC5Y)

### [Embedded Linux with FPGA   Device Drivers Basic #03](https://www.youtube.com/watch?v=h-ZP98qhEM8)

### [#4 Verilog, Linux, Qsys](https://www.youtube.com/watch?v=1kjhMJZo_KU)

### [Physics for Game Programmers: Understanding Constraints](https://www.youtube.com/watch?v=SHinxAhv1ZE)

### [Intro to Game Physics](https://www.youtube.com/watch?v=wPKzwSxyhTI)

### [CppCon 2015: Fedor Pikus “C++ Metaprogramming: Journey from simple to insanity and back"](https://www.youtube.com/watch?v=CZi6QqZSbFg)

### [Lec 1 | MIT 6.450 Principles of Digital Communications I, Fall 2006](https://www.youtube.com/watch?v=KXFF8m4uGDc)

### [Introduction to computer graphics, lecture 1:  Introduction](https://www.youtube.com/watch?v=E1-_15Vfddk)

### [The Physics of Superconducting Devices - Anthony Leggett - Lecture #1 - 2014](https://www.youtube.com/watch?v=ZSmqdlHS1oU)

### [Topological Superconductivity in Quantum Materials and Devices](https://www.youtube.com/watch?v=PGM-hAGV-f8)

### [Machine Learning Quantum Phases of Matter - Simon Trebst - May 31, 2017](https://www.youtube.com/watch?v=24NAfIXoaYg)

### [Topological States of Quantum Condensed Matter: Duncan Haldane](https://www.youtube.com/watch?v=0TvpCrejj8c)

### [1. Resonance I](https://www.youtube.com/watch?v=iwQ49oG-DO8)

### [Lasers & Optoelectronics Lecture 1: Laser Basics (Cornell ECE4300 Fall 2016)](https://www.youtube.com/watch?v=f8nG9kPcFv0)

### [Lec 1 | MIT 2.71 Optics, Spring 2009](https://www.youtube.com/watch?v=IYBYmOVmICg)

### [Introducing MRI: The Basics (1 of 56)](https://www.youtube.com/watch?v=35gfOtjRcic)

### [Lecture 12 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=sVP6LrX-Nzs)

### [Lecture 11 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=Tpz5Sn7ZK9M)

### [Real-time optimization algorithms for dynamic walking, running, and manipulating robots](https://www.youtube.com/watch?v=u2HkPkzSlPY)

### [2. Resonance II](https://www.youtube.com/watch?v=TcvY8Nt0ZGA)

### [Lec 2 | MIT 6.450 Principles of Digital Communications I, Fall 2006](https://www.youtube.com/watch?v=503wzjz8czs)

### [VIVADO HLS Training - Introduction #01](https://www.youtube.com/watch?v=kgae3Wzqngs)

### [Anthony Cowley - Framing the Discussion with EDSLs](https://www.youtube.com/watch?v=_KioQRICpmo)

### [Lecture 13 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=_620Nyyh38M)

### [The Physics of Superconducting Devices - Anthony Leggett - Lecture #6 - 2014](https://www.youtube.com/watch?v=r8yxThWgMmI)

### [Lecture 2: Modular Arithmetic and Historical Ciphers by Christof Paar](https://www.youtube.com/watch?v=W1SY6qKZrUk)

### [Lecture 3: Stream Ciphers, Random Numbers and the One Time Pad by Christof Paar](https://www.youtube.com/watch?v=AELVJL0axRs)

### [Modern Cryptography with Haskell by Stephen Diehl](https://www.youtube.com/watch?v=BFA-mQEHNhc)

### [Efficiently coding for modern CPUs by Edward Kmett](https://www.youtube.com/watch?v=KzqNQMpRbac)

### [Lecture 16 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=jmQxjUr4J0o)

### [Lecture 18 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=_44Vvtix_qU)

### [Lecture 19 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=LS_P7VyZkH4)

### [Lecture 4: Stream Ciphers and Linear Feedback Shift Registers by Christof Paar](https://www.youtube.com/watch?v=sKUhFpVxNWc)

### [Haskell Live-Coding, Session 2.1, Q&A](https://www.youtube.com/watch?v=d1T9JhurjE0)

### [Lecture 20 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=uNBQV_Xm1TA)

### [Lecture 21 | MIT 6.832  (Underactuated Robotics), Spring 2018](https://www.youtube.com/watch?v=-nOYnUkxSHI)

### [ICSP 2016:  Introduction to Stochastic Programming (Part I)](https://www.youtube.com/watch?v=bB-CSHHFsUU)

### [Stochastic Optimization Models on Power Systems | Camila Metello and Joaquim Garcia | JuliaCon 2017](https://www.youtube.com/watch?v=W6y0_qMtl00)

### [The State of the Type System | Jeff Bezanson | JuliaCon 2017](https://www.youtube.com/watch?v=Z2LtJUe1q8c)

### [Solving QBF by Counterexample-Guided Abstraction Refinement](https://www.youtube.com/watch?v=i2CQDEI05W8)

### [CPP-06 Modern C++: Static, Numbers, Arrays, Non-owning pointers, Classes (2018, Igor)](https://www.youtube.com/watch?v=mIrOcFf2crk)

### [06 - Miguel A. Morales - Wavefunction Optimization](https://www.youtube.com/watch?v=tiPuRrtI12Y)

### [J  Bollinger Trapped ion Quantum Simulation, Computing and Sensing I July 2](https://www.youtube.com/watch?v=I6goyHHYdkI)

---

## prog10.json

### [Greybeard Qualification (Linux Internals) part 1: Process Structure and IPC](https://www.youtube.com/watch?v=5osOHhBWKOQ)

### ["Simple Code" Follow-up Part 1: A (Very) Simplified CPU Diagram](https://www.youtube.com/watch?v=8VakkEFOiJc)

### [Lecture 1: MIT 6.800/6.843 Robotic Manipulation (Fall 2021) | "Anatomy of a manipulation system"](https://www.youtube.com/watch?v=pitFVp5BbCc)

### [Algebraic geometry 1 Introduction](https://www.youtube.com/watch?v=JZKDmTIFR7A)

### [Rebuilding Operating Systems with Functional Principles | Dr Anil Madhavapeddy (Lecture 1)](https://www.youtube.com/watch?v=7twZNoezjZI)

---

## prog8.json

### [Lecture 20 | MIT 6.832  (Underactuated Robotics), Spring 2019](https://www.youtube.com/watch?v=bw71ElvpokE)

### [Feedback Control of Hybrid Dynamical Systems](https://www.youtube.com/watch?v=08JJFK9lhQk)

### [Real-Time Decision Making in Hybrid Systems](https://www.youtube.com/watch?v=6y-dWHChVxw)

### [Validation, Synthesis and Optimization for Cyber-Physical Systems](https://www.youtube.com/watch?v=GYcFfFhYIM0)

### [Gurobi Optimization Application Demos](https://www.youtube.com/watch?v=Vu6HIF3SqWY)

### [TSS_20170717 02 - Parametric Optimisation, Introduction to PLC](https://www.youtube.com/watch?v=9d46lIP6kTc)

### [Backpack to Work: Towards Backpack in Practice](https://www.youtube.com/watch?v=A3ehG4GQpxU)

### [Grothendieck's 1973 topos lectures - C. McLarty](https://www.youtube.com/watch?v=5AR55ZsHmKI)

### [David Spivak: Monadic Decision Processes for Hierarchical Planning](https://www.youtube.com/watch?v=tVtDs2ZcQvA)

### [Funnel Libraries for Real-Time Robust Feedback Motion Planning (Anirudha Majumdar)](https://www.youtube.com/watch?v=BgK4iTv5bjw)

### [Neutron Stars and Black Holes (Lecture - 01: Diffuse Stars) by G Srinivasan](https://www.youtube.com/watch?v=ipWsFJ_t8vA)

### [ICAPS 2018: David Speck on "Symbolic Planning with Edge-Valued Multi-Valued Decision Diagrams"](https://www.youtube.com/watch?v=WKM59cMPqVI)

### [The design of functional numerical software - Dr Richard Mortier, University of Cambridge](https://www.youtube.com/watch?v=EbETMvEgvHE)

### [HELIX: A Case Study of a Formal Verification of High Performance Program Generation](https://www.youtube.com/watch?v=o7f2dQ4qpnQ)

### [Preventing Data Races with Refinement Types](https://www.youtube.com/watch?v=wQdchyaRe0A)

### [TSS_20170719 02 - Arduino, Part II](https://www.youtube.com/watch?v=GLM_zCbd9mo)

### [Meta-F*: Proof Automation with SMT, Tactics, and Metaprograms - Nikhil Swamy](https://www.youtube.com/watch?v=46f5skPRic0)

### [Cody Roux - SMT for DSLs: a Tutorial](https://www.youtube.com/watch?v=2rhrxkNtrM4)

### [Interactive Theorem Proving with Lean](https://www.youtube.com/watch?v=tU5HfVc2nR8)

### [[LLVM Social] The Lean Theorem Prover](https://www.youtube.com/watch?v=ZFjxVTIw5-M)

### [Towards Lean 4: An Optimized Object Model for an Interactive Theorem Prover](https://www.youtube.com/watch?v=Bv0CXyhbJ5s)

### [Isabelle meets Compilers - 13.09.2018](https://www.youtube.com/watch?v=bIGDIrWt5e0)

### [Procedural Macros in Rust (part 1)](https://www.youtube.com/watch?v=geovSK3wMB8)

### [FA'18 01: Overview - Logical Foundations of Cyber-Physical Systems](https://www.youtube.com/watch?v=EZ20CLwG6m8)

### [VeriPhy: Verified Controller Executables from Verified Cyber-Physical System Models](https://www.youtube.com/watch?v=Qu31njE9xic)

### [Rust at speed — building a fast concurrent database](https://www.youtube.com/watch?v=s19G6n0UjsM)

### [Russ Tedrake (MIT): "Learning manipulation — and why I (still) like F=ma"](https://www.youtube.com/watch?v=Tyz1jRfyWgY)

### [Automated Economic Reasoning with Quantifier Elimination](https://www.youtube.com/watch?v=CekdFUaEhxc)

### [ICML 2019 A Tutorial on Attention in Deep Learning](https://www.youtube.com/watch?v=nS1Lse2B48w)

### [ICAPS 2018: Richard E. Korf on "What is the Right Search Algorithm for My Problem?"](https://www.youtube.com/watch?v=X6qCBcubZIE)

### [ICAPS 2018: Hannah Bast on "Route Planning in Large Transportation Networks: Surprisingly Hard ..."](https://www.youtube.com/watch?v=B3wKfJAVRkg)

### [ICAPS 2018: Chiara Piacentini on "Compiling Optimal Numeric Planning to Mixed Integer Linear ..."](https://www.youtube.com/watch?v=9LTey9WChdo)

### [Program Synthesis using Conflict-Driven Learning](https://www.youtube.com/watch?v=fV6iv3GLyuY)

### [ICML 2019 Tutorial: Meta-Learning: from Few-Shot Learning to Rapid Reinforcement Learning (Part 1)](https://www.youtube.com/watch?v=DijI4XrhqNo)

### [Formally Verified Cryptographic Web Applications in WebAssembly](https://www.youtube.com/watch?v=VpFY4g4QPnY)

### [Applied Mixed Integer Programming: Beyond 'The Optimum'](https://www.youtube.com/watch?v=zWj1Lcm7izo)

### [Parallelism in Linear and Mixed Integer Programming](https://www.youtube.com/watch?v=PhEhQhGDCvs)

### [Stanford Seminar - A Superscalar Out-of-Order x86 Soft Processor for FPGA](https://www.youtube.com/watch?v=vhHR6fNHyG8)

### [Introduction to Formal Verification with Symbiotic EDA Open Source Tools](https://www.youtube.com/watch?v=H3tsP9tjYdY)

### [Taking Resources to the Type Level – Vilem-Benjamin Liepelt](https://www.youtube.com/watch?v=han6vHzPLsY)

### [Lambda World 2018 - MirageOS, towards a smaller and safer OS - Romain Calascibetta](https://www.youtube.com/watch?v=urG5BjvjW18)

### [Functors of the World, Unite!](https://www.youtube.com/watch?v=8k7YH9st_8U)

### [Making Algorithmic Music](https://www.youtube.com/watch?v=9Fg54XAr044)

### [Stuck macros: deterministically interleaving macro-expansion and typechecking](https://www.youtube.com/watch?v=nUvKoG_V_U0)

### [Yes, IHaskell Can Do That!](https://www.youtube.com/watch?v=nYBW4ExtNvo)

### [Type Driven Secure Enclave Development using Idris](https://www.youtube.com/watch?v=o9Y1Cd794Xc)

### [A Tase Of ATS](https://www.youtube.com/watch?v=ADN6B1Wk5Ts)

### [The Best Refactoring You’ve Never Heard Of](https://www.youtube.com/watch?v=vNwukfhsOME)

### [Bidirectional Type Checking](https://www.youtube.com/watch?v=utyBNDj7s2w)

### [Bowl Full of Lentils](https://www.youtube.com/watch?v=a-RltqZKqLI)

### [Metamaterials and Topological Mechanics (Lecture - 01) by Tom Lubensky](https://www.youtube.com/watch?v=sEaJ0LlXmbE)

### [Xavier Caruso: Ore polynomials and application to coding theory](https://www.youtube.com/watch?v=n4ZAmXysJvU)

### [Edward Kmett - Logic Programming in Haskell 3/4](https://www.youtube.com/watch?v=c3UE41eYXHA)

### [Edward Kmett - Logic Programming in Haskell 4/4](https://www.youtube.com/watch?v=TnohBRvoUJk)

### [SAS2018 - Deductive Verification in Decidable Fragments with Ivy (by K. McMillan and O. Padon)](https://www.youtube.com/watch?v=CE1mcjqea0A)

### [Verification beyond programs - Rustan Leino](https://www.youtube.com/watch?v=2-qJA6ozcJ8)

### [What's Algebraic About Algebraic Effects and Handlers? [1/2] - Andrej Bauer - OPLSS 2018](https://www.youtube.com/watch?v=atYp386EGo8)

### [Static Program Analysis (part 1/2) - Anders Møller - PLISS 2019](https://www.youtube.com/watch?v=Lr4cMmaJHrg)

### [Heat Methods in Geometry Processing](https://www.youtube.com/watch?v=4IZ-ykGnIRc)

### [seL4 Is Free – What Does This Mean For You?](https://www.youtube.com/watch?v=lRndE7rSXiI)

### [Discretization of Elliptic Differential Equations Using Sparse Grids... (Cristoph Pflaum)](https://www.youtube.com/watch?v=nsn1QCxTT-Y)

### [6.858 Fall 2014 Lecture 10: Symbolic execution](https://www.youtube.com/watch?v=mffhPgsl8Ws)

### [DEF CON 23 - Shoshitaishvili and Wang - Angry Hacking: The next gen of binary analysis](https://www.youtube.com/watch?v=oznsT-ptAbk)

### [DEF CON 25 - Yan Shoshitaishvili - 25 Years of Program Analysis](https://www.youtube.com/watch?v=XL9kWQ3YpLo)

### [Angr - a powerful binary analysis platform for CTFs. The Cyber Grand Challenge](https://www.youtube.com/watch?v=Wx2RhKI7TIU)

### [Demystifying Binary Reverse Engineering](https://www.youtube.com/watch?v=q_jBaPXpr_k)

### [Introduction to Automated Binary Analysis  (GPN17)](https://www.youtube.com/watch?v=wCqKZmy6jiI)

### [SoK: (State of) The Art of War: Offensive Techniques in Binary Analysis](https://www.youtube.com/watch?v=ONuLsVcaHB8)

### [Using Static Binary Analysis To Find Vulnerabilities And Backdoors In Firmware](https://www.youtube.com/watch?v=Fi_S2F7ud_g)

### [Toward Efficient Gradual Typing for Structural Types by Deyaaeldeen Almahallawi](https://www.youtube.com/watch?v=3WrddtlNCCY)

### [Galois Inc. Tech Talk: Formal Hardware Verification: Asynchronous, Analog, Mixed-Signal, and Mixed-T](https://www.youtube.com/watch?v=W67ugWhDxN4)

### [Warsaw Quantum Computing Group, Ep III, "Introduction to programming quantum computers using pyQuil"](https://www.youtube.com/watch?v=FPGcmK0ftXU)

### [Simon Peyton Jones how GHC type inference engine actually works](https://www.youtube.com/watch?v=x3evzO8O9e8)

### [Data-Centric Abstractions and Operator Formulation of Algorithms - Keshav Pingali - OPLSS 2018](https://www.youtube.com/watch?v=GwLC7oeo1d4)

### [Brendan Fong: A categorical introduction to profunctor optics, Part 1.](https://www.youtube.com/watch?v=7rHV78fttrI)

### [Introduction to Incr_dom: Writing Dynamic Web Apps in OCaml](https://www.youtube.com/watch?v=h_e5pPKI0K4)

### [OCaml All The Way Down](https://www.youtube.com/watch?v=X1cgRXhpQLY)

### [BOB Summer 2019 - Henning Thielemann, Expressive Linear Algebra in Haskell](https://www.youtube.com/watch?v=Y2bM3n03z_I)

### [NAMPI v2 - Armando Solar-Lezama - Program synthesis and ML join forces](https://www.youtube.com/watch?v=-LY-k_l819k)

### [Ashley Montanaro: Applying quantum algorithms to constraint satisfaction problems](https://www.youtube.com/watch?v=3XuT0Kjif8w)

### ["Easy Abstract Interpretation with SPARTA" by Arnaud Venet and Jez Ng](https://www.youtube.com/watch?v=_fA7vkVJhF8)

### ["Performance Matters" by Emery Berger](https://www.youtube.com/watch?v=r-TLSBdHe1A)

### [RustBelt: Logical Foundations for the Future of Safe Systems Programming](https://www.youtube.com/watch?v=1GjSfyijaxo)

### [Writing Verified Software for Production - Rustan Leino - OPLSS 2019](https://www.youtube.com/watch?v=8CIYKpCNMHc)

### [Analysis and Synthesis of Floating-Point Routines - Zvonimir Rakamaric](https://www.youtube.com/watch?v=S5hC9EbwNlU)

### [Unboxed Types for OCaml](https://www.youtube.com/watch?v=RV-4Xddk0Yc)

### [[PyEMMA 2018] Introduction to Markov state models](https://www.youtube.com/watch?v=YXppP_QTut8)

### [Benjamin Recht: Optimization Perspectives on Learning to Control (ICML 2018 tutorial)](https://www.youtube.com/watch?v=nF2-39a29Pw)

### [2019 ADSI Summer Workshop: Algorithmic Foundations of Learning and Control, Ben Recht](https://www.youtube.com/watch?v=wsjQSMMFJbM)

### [A gentle introduction to network science: Dr Renaud Lambiotte, University of Oxford](https://www.youtube.com/watch?v=L6CqqlILBCI)

### [Deep learning for technical computations and equation solving](https://www.youtube.com/watch?v=B9ugHg9Sy6g)

### [Topological quantum phases - Alexei Kitaev](https://www.youtube.com/watch?v=W2vUbTR2RWQ)

---

## prog4.json

### [Chordal Graphs and Sparse Semidefinite Optimization](https://www.youtube.com/watch?v=py-7rWTERVU)

### [Circle Packing and Its Applications](https://www.youtube.com/watch?v=WEmTEE9wjCc)

### [Matroids as a Theory of Independence by Federico Ardila](https://www.youtube.com/watch?v=4EvpzV_3RXI)

### [Bernd Sturmfels(Univ. of California, Berkeley) / Lecture 5 : Matroids and Linear Spaces](https://www.youtube.com/watch?v=Yqhhm8MsHzU)

### [Federico Ardila: "Algebraic Structures on Polytopes"](https://www.youtube.com/watch?v=_sEhFx5mkec)

### [Avi Wigderson: "Proving Algebraic Identities"](https://www.youtube.com/watch?v=zS0xd7cQnuY)

### [Tamara G. Kolda: "Tensor Decomposition"](https://www.youtube.com/watch?v=L8uT6hgMt00)

### [William Cook: "Information, Computation, Optimization..."](https://www.youtube.com/watch?v=q8nQTNvCrjE)

### [Factorization-based Sparse Solvers and Preconditions Lecture 2](https://www.youtube.com/watch?v=ucWkWxRP2t8)

### [Factorization-based Sparse Solvers and Preconditions, Lecture 3](https://www.youtube.com/watch?v=pXfXivkL4xU)

### [Tutorial: Gait and Trajectory Optimization for Legged Robots](https://www.youtube.com/watch?v=KhWuLvb934g)

### [Introduction to Optimization and Optimal Control using the software packages CasADi and ACADO](https://www.youtube.com/watch?v=JC6PNjndQ_c)

### ["Stable Fluids" by Dan Piponi [PWLConf 2018]](https://www.youtube.com/watch?v=766obijdpuU)

### [AI for Imperfect-Information Games: Beating Top Humans in No-Limit Poker](https://www.youtube.com/watch?v=McV4a6umbAY)

### [Ankur Moitra : Tensor Decompositions and their Applications](https://www.youtube.com/watch?v=HcIN27_WqPU)

### [The moment-SOS hierarchy – Jean Lasserre – ICM2018](https://www.youtube.com/watch?v=yGHoq8CPYDY)

### [New Frontiers in Imitation Learning](https://www.youtube.com/watch?v=teyGpr2Dgm4)

### [Submodular Optimization and Machine Learning - Part 1](https://www.youtube.com/watch?v=LceBpKjg10I)

### [Totally Unimodular Matrices in Linear Programming - Nate Veldt](https://www.youtube.com/watch?v=Fmjy74c-R-I)

### [Matrix Representation of FMM - Difeng Cai](https://www.youtube.com/watch?v=AWy0XJ1tGC8)

### [HSS Solvers - Jimmy Vogel](https://www.youtube.com/watch?v=xGV8r0SVw5E)

### [Lecture  2 . Matroids (Federico Ardila)](https://www.youtube.com/watch?v=-tj0T5WihzI)

### [SOS Seminar Lecture 9 -  SOS and the Unique Games conjecture—a love hate relationship](https://www.youtube.com/watch?v=EqBQw-J1rxI)

### [SOS Seminar lecture 4 -  Sparsest cut problem and ARV algorithm (updated)](https://www.youtube.com/watch?v=k7-0N4tGE6I)

### [Robert Sapolsky: The Biology of Humans at Our Best and Worst](https://www.youtube.com/watch?v=GRYcSuyLiJk)

### [Stanford's Robert Sapolsky On Depression](https://www.youtube.com/watch?v=TIcf-2AFHgw)

### [Tensor Decompositions for Learning Hidden Variable Models](https://www.youtube.com/watch?v=ovPiVkDLiUs)

### [Princeton Day of Optimization 2018: Taking Control by Convex Optimization by Elad Hazan](https://www.youtube.com/watch?v=K_6KCsf-eco)

### [Princeton Day of Optimization 2018: Graph Structure in Polynomial Systems Chordal … by Pablo Parrilo](https://www.youtube.com/watch?v=jV1NSN44vQU)

### [Using Computational Group Theory](https://www.youtube.com/watch?v=pJ9H0apyouc)

### [Lambda World 2018 - Opening Keynote by Edward Kmett](https://www.youtube.com/watch?v=HGi5AxmQUwU)

### [Lecture 4 . Hopf Algebras and Combinatorics (Federico Ardila)](https://www.youtube.com/watch?v=cVW_wLe2GdQ)

### [Avi Wigderson: "Alternate Minimization and Scaling Algorithms"](https://www.youtube.com/watch?v=OeefpxMRU7g)

### [Robert Bryant: "The Concept of Holonomy"](https://www.youtube.com/watch?v=QORRJEkhw6s)

### [László Babai: "Groups, Graphs and Algorithms"](https://www.youtube.com/watch?v=-VeyhCHHPUo)

### [Solving optimization problems containing piecewise linear functions (Joey Huchette, MIT)](https://www.youtube.com/watch?v=yiWx52yVVzM)

### [Discrete Optimization, Shmuel Onn, MSRI Berkeley, Lecture 1 of 7](https://www.youtube.com/watch?v=Y6TNG1W5Bp0)

### [Algebraic number theory and rings I  | Math History | NJ Wildberger](https://www.youtube.com/watch?v=H8xBlLWdzBE)

### [Peter Zoller: Introduction to quantum optics - Lecture 1](https://www.youtube.com/watch?v=zEAwL9GAPCo)

### [RI Seminar: Oliver Kroemer : Learning Robot Manipulation Skills...](https://www.youtube.com/watch?v=drCfLNTB0Ro)

### [Lecture 1  .  Polytopes (Federico Ardila)](https://www.youtube.com/watch?v=xpv8eco4u4s)

### [Lecture 5 . Hopf Algebras and Combinatorics (Federico Ardila)](https://www.youtube.com/watch?v=PPexiDR4r0Y)

### [Jesus De Loera "One hundred years of Helly’s Theorem"](https://www.youtube.com/watch?v=wmASlGyf3x4)

### [Jesús de Loera: "Variations of Carathéodory theorem for Integer Optimization"](https://www.youtube.com/watch?v=BKn5oVsthVI)

### [ICML 2017 Tutorial: Recent Advances in Stochastic Convex and Non-Convex Optimization (audio fixed)](https://www.youtube.com/watch?v=jPjhiaeYruQ)

### [Algebraic number theory and rings II | Math History | NJ Wildberger](https://www.youtube.com/watch?v=GMZoXXaOFeQ)

### [02. Algebraic geometry - Sheaves and morphisms (Diana Carolina Castañeda)](https://www.youtube.com/watch?v=45ykUAY4s04)

### [Manifolds as Haskell types](https://www.youtube.com/watch?v=sdBssEg_fjo)

### [Daisy - A framework for sound accuracy analysis and optimization of numerical programs](https://www.youtube.com/watch?v=0SUvyhbFjeg)

### [On the Calculation of Functions in the Algebra of Physical Space](https://www.youtube.com/watch?v=etW0XZqiv4Q)

### [Exact Real Arithmetic for Geometry](https://www.youtube.com/watch?v=pMDoNfKXYZg)

---

## prog2.json

### [LP/SDP Hierarchies and Sum of Squares Proofs 3](https://www.youtube.com/watch?v=zbAaoyE9riU)

### [JuMP-dev 2018 | EMP.jl, a package for modelling Extended Mathematical Programming | Olivier Huber](https://www.youtube.com/watch?v=u7vASGAJYlY)

### [JuMP-dev 2018 | Topology Optimization and JuMP | Mohamed Tarek](https://www.youtube.com/watch?v=zNZ_bw1ti00)

### [NeuroSAT: Learning a SAT Solver from Single-Bit Supervision](https://www.youtube.com/watch?v=EqvzIGY_bI4)

### [Solving Max-SAT by Decoupling Optimization and Satisfaction](https://www.youtube.com/watch?v=H8IyTcEtzDA)

### [Donald Knuth: "The Art of Computer Programming: Satisfiability and Combinatorics"](https://www.youtube.com/watch?v=g4lhrVPDUG0)

### [Category Theory III 4.2, Monad algebras part 3](https://www.youtube.com/watch?v=9f8PumwS2gU)

### [Bedrock: A Software Development Ecosystem Inside a Proof Assistant](https://www.youtube.com/watch?v=BSyrp-iYBMo)

### [Day 1 Part 1: Introductory Intel x86: Architecture, Assembly, Applications](https://www.youtube.com/watch?v=H4Z0S9ZbC0g)

### [Day 1 Part 1: Intro to Software RE (Reverse Engineering)](https://www.youtube.com/watch?v=byK0tXH5axQ)

### [Category Theory III 5.1, Eilenberg Moore and Lawvere](https://www.youtube.com/watch?v=5PaxKu2TXno)

### [Category Theory III 5.2, Lawvere Theories](https://www.youtube.com/watch?v=zCTAn_nIrS0)

### [The Tensor Algebra Compiler](https://www.youtube.com/watch?v=yAtG64qV2nM)

### [Introduction to LLVM Building simple program analysis tools and instrumentation](https://www.youtube.com/watch?v=VKIv_Bkp4pk)

### [Understanding Compiler Optimization - Chandler Carruth - Opening Keynote Meeting C++ 2015](https://www.youtube.com/watch?v=FnGCDLhaxKU)

### [Semidefinite Programming Hierarchies I: Convex Relaxations for Hard Optimization Problems](https://www.youtube.com/watch?v=oOr7N1zsNLI)

### [CS410 2017 Lecture 6 (A Comedy of (entirely non-deliberate) Errors)](https://www.youtube.com/watch?v=RW4aC_6n0yQ)

### [Galois, Inc. Tech Talk: Vellvm - Verifying the LLVM (Steve Zdancewic)](https://www.youtube.com/watch?v=qGpRKkP8gec)

### [Richard Eisenberg on Dependent Types](https://www.youtube.com/watch?v=XJ8hm3Tq2k8)

### [Distributed Optimization via Alternating Direction Method of Multipliers](https://www.youtube.com/watch?v=Xg0ozgCXXB8)

### [Type Theory Study Group, Special Topics on ABTs, Implementation and Theory with Jon Sterling](https://www.youtube.com/watch?v=jIre_aCCgWM)

### [SMT Solving in Haskell - Matt Peddie](https://www.youtube.com/watch?v=luaPkv5Rnpk)

### [Unification](https://www.youtube.com/watch?v=rcmqzEbW1UE)

### [[In English] Functional Thursday #Special - Having an Effect by Oleg Kiselyov](https://www.youtube.com/watch?v=GhERMBT7u4w)

### [Multiple Concepts of Equality in the New Foundations of Mathematics by Vladimir Voevodsky](https://www.youtube.com/watch?v=slVcTtwX_Sk)

### [Naïve Type Theory by Thorsten Altenkirch (University of Nottingham, UK)](https://www.youtube.com/watch?v=bNG53SA4n48)

### ["Elements of Mathematics" in the Digital Age by Marc Bezem (Universitetet i Bergen, Norway)](https://www.youtube.com/watch?v=8uUof2vYnQk)

### [On Proofs of Equality as Paths by Andrew Pitts (University of Cambridge, UK)](https://www.youtube.com/watch?v=321h4VJgt84)

### [Thomas Ball -  Advances in Automated Theorem Proving](https://www.youtube.com/watch?v=unXzJEc3Pvk)

### [12  An Agda formalization of the transitive closure of block matrices](https://www.youtube.com/watch?v=ts48ZYEuj4I)

### [ICFP 2012.  Lee Pike:  Experience Report - a Do-It-Yourself High-Assurance Compiler.](https://www.youtube.com/watch?v=7zXhP--9axQ)

### [How Helpful is Network Coding?](https://www.youtube.com/watch?v=_0tiUsYL2Rg)

### [Networking coding - Muriel Medart, MIT](https://www.youtube.com/watch?v=3-CiRgH0knw)

### [Fundamentals of Distributed Algorithms - Part 1](https://www.youtube.com/watch?v=SmyUBbuXfxI)

### [Fundamentals of Distributed Algorithms - Part 2](https://www.youtube.com/watch?v=6EEgWmyl-IM)

### [ITA 2010 - Multisource Network Coding, Raymond W. Yeung](https://www.youtube.com/watch?v=8p_wpPm41EE)

### [A Little Taste of Dependent Types (David Thrane Christiansen)](https://www.youtube.com/watch?v=1BWYy2-WM-o)

### [Univalence from a computer science point-of-view - Dan Licata](https://www.youtube.com/watch?v=j5RIZAzooAg)

### [CSE574-16-11: Wireless Protocols for IoT Part II: IEEE 802.15.4 Wireless Personal Area Networks](https://www.youtube.com/watch?v=TygazWNxlRI)

### [Computational Type Theory [1/5] - Robert Harper - OPLSS 2018](https://www.youtube.com/watch?v=LE0SSLizYUI)

### [Purely Functional Array Programming [1/3] - Gabrielle Keller - OPLSS 2018](https://www.youtube.com/watch?v=RCPsNceeXk4)

### [Barak A. Pearlmutter – Automatic Differentiation: History and Headroom](https://www.youtube.com/watch?v=zqaJeKZXS1U)

### [Automatic differentiation and machine learning](https://www.youtube.com/watch?v=pdSCHtPJ4B0)

### [DeepSpec Summer School, Coq Intensive, Part 9 (July 15, 2017)](https://www.youtube.com/watch?v=reM6GSPwEw0)

### [Parallel Algorithms [1/5] - Umut Acar - OPLSS 2018](https://www.youtube.com/watch?v=8ZeGs5SBOFU)

### [Extending F* in F*: Proof automation and Metaprogramming for Typeclasses](https://www.youtube.com/watch?v=2zQLfQ7eyPA)

### [Formal Verification of Verilog HDL with Yosys-SMTBMC (33c3)](https://www.youtube.com/watch?v=VJsMLPGg4U4)

### [Multi-Party Computation: From Theory to Practice](https://www.youtube.com/watch?v=pNNLAEygPQI)

### [Introduction to Grobner Bases - Prof. Bernd Sturmfels](https://www.youtube.com/watch?v=TNO5WuxuNak)

### [Nonlinear algebra, Lecture 1: "Polynomials, Ideals, and Groebner Bases", by Bernd Sturmfels](https://www.youtube.com/watch?v=1EryuvBLY80)

### [Marta Kwiatkowska, "Probabilistic model checking of labelled Markov processes"](https://www.youtube.com/watch?v=SONj64dXjUo)

---

## prog5.json

### [A Haskell Interface to SUNDIALS via inline-c](https://www.youtube.com/watch?v=k1Gych2os0s)

### [David Spivak - Category Theory - Part 1 of 6 - λC 2017](https://www.youtube.com/watch?v=IBeceQHz2x8)

### [Lambda World 2018 - Introduction to the Unison programming language - Rúnar Bjarnason](https://www.youtube.com/watch?v=rp_Eild1aq8)

### [The Limits of Proof](https://www.youtube.com/watch?v=-_9sbSJz3-w)

### [Silvio Micali: Proofs, Knowledge, and Computation](https://www.youtube.com/watch?v=WSuUTLqqLIU)

### [Shafi Goldwasser: From Basic Idea to Impact: the story of modern cryptography](https://www.youtube.com/watch?v=FGtsqEwANWY)

### [IFL 2012. Fritz Henglein: Generic sorting and partitioning in linear time and fully abstractly](https://www.youtube.com/watch?v=sz9ZlZIRDAg)

### [Haskell Live-Coding, Session 15, Back from ICFP](https://www.youtube.com/watch?v=JYWSqT1FIug)

### [Sergey Bravyi: Improved classical simulation of quantum circuits dominated by Clifford gates](https://www.youtube.com/watch?v=MqVTcuLw9Dc)

### [Introduction to Information Theory - Edward Witten](https://www.youtube.com/watch?v=XYugyhoohhY)

### [Propositional Proof Complexity: Fifteen (or so) Years After - Alexander Razborov](https://www.youtube.com/watch?v=7LfW6VTW8zo)

### [Proof complexity - an introduction - Avi Wigderson](https://www.youtube.com/watch?v=9oHTkDdmax0)

### [Optimization in dynamical systems - Amir Ali Ahmadi](https://www.youtube.com/watch?v=FdD9fxSTF5I)

### [Robust sensitivity - Shachar Lovett](https://www.youtube.com/watch?v=DXKIEh2veec)

### [Outlier-Robust Estimation via Sum-of-Squares - Pravesh Kothari](https://www.youtube.com/watch?v=9s5kkIn5TsQ)

### [Algebraic combinatorics: applications to statistical mechanics and complexity theory - Greta Panova](https://www.youtube.com/watch?v=dGGrTt81K9s)

### [Noncommutative probability for computer scientists - Adam Marcus](https://www.youtube.com/watch?v=TVxedA0YCyI)

### [Rigorous RG: a provably efficient and possibly practical algorithm for... - Umesh Vazirani](https://www.youtube.com/watch?v=idbLkc0rUlY)

### [An update on SymbiFlow - a multiplatform FPGA project - Tim Ansell - ORConf 2018](https://www.youtube.com/watch?v=CI1lpbt2Hz8)

### [Nonlinear algebra, Lecture 8: "Tensors", by Bernd Sturmfels and Mateusz Michalek](https://www.youtube.com/watch?v=L261Ioew4MU)

### [Invariant Theory for Computer Scientists](https://www.youtube.com/watch?v=AKOYfk4VJpA)

### [An introduction to Invariant Theory - Harm Derksen](https://www.youtube.com/watch?v=3jksqrYuvuk)

### [Tutorial 2: Algorithmic Invariant Theory](https://www.youtube.com/watch?v=s1wH6GOWANc)

### [Tutorial 3: Geometric Invariant Theory](https://www.youtube.com/watch?v=CJXRhnjMXjU)

### [Semidefinite Hierarchies in Quantum Information](https://www.youtube.com/watch?v=QcCTKmA4aFc)

### [Stanford Lecture: Dancing Links](https://www.youtube.com/watch?v=t9OcDYfHqOk)

### [Stanford Seminar: Beyond Floating Point: Next Generation Computer Arithmetic](https://www.youtube.com/watch?v=aP0Y1uAA-2Y)

### [Alberto Bemporad | Embedded Model Predictive Control](https://www.youtube.com/watch?v=ugeCx1sytNU)

### [Cassette: Dynamic, Context-Specific Compiler Pass Injection for Julia | J Revels | JuliaCon 2018](https://www.youtube.com/watch?v=_E2zEzNEy-8)

### [Flux: The Elegant Machine Learning Library | Mike Innes | JuliaCon 2018](https://www.youtube.com/watch?v=R81pmvTP_Ik)

### [Ju Gonçalves - Abstract nonsense | Code Mesh LDN 18](https://www.youtube.com/watch?v=mgLouh5nJO8)

### [Hillel Wayne - Everything about distributed systems is terrible | Code Mesh LDN 18](https://www.youtube.com/watch?v=tfnldxWlOhM)

### [Advanced Machine Learning Day 3: Neural Architecture Search](https://www.youtube.com/watch?v=wL-p5cjDG64)

### [Advanced Machine Learning Day 3: Neural Program Synthesis](https://www.youtube.com/watch?v=nlgA2gnwscQ)

### [Lesson 1: Deep Learning 2018](https://www.youtube.com/watch?v=IPBSB1HLNLo)

### [Exact Real Arithmetic for Geometry](https://www.youtube.com/watch?v=pMDoNfKXYZg)

### [Solving Simple Stochastic Optimization Problems with Gurobi](https://www.youtube.com/watch?v=Jb4a8T5qyVQ)

### [CTNT 2018 - "Computational Number Theory" (Lecture 1) by Harris Daniels](https://www.youtube.com/watch?v=aoGmj2cxfKQ)

### [Fabian Immler : Verified numerics for ODEs in Isabelle/HOL](https://www.youtube.com/watch?v=1XjkRxPTaUE)

### [Laurent Théry : Proof and computation in Coq](https://www.youtube.com/watch?v=uBB7k0BoaS8)

### [Norbert Müller : Wrapping in exact real arithmetic](https://www.youtube.com/watch?v=f8fivVYdGlg)

### [Eva Darulova : Programming with numerical uncertainties](https://www.youtube.com/watch?v=el4zbqRzKZ8)

### [Sylvie Boldo : Formal verification of numerical analysis programs](https://www.youtube.com/watch?v=7MDwpwD6Ts4)

### [Fiat Cryptography: Automatic Correct-by-Construction Generation of Low-Level Cryptographic Code](https://www.youtube.com/watch?v=PVHDIiqvBaU)

### [Negative Dependence, Stable Polynomials, and All That](https://www.youtube.com/watch?v=R9pjzgHZ5kI)

### [HELIX: A Case Study of a Formal Verification of High Performance Program Generation](https://www.youtube.com/watch?v=o7f2dQ4qpnQ)

### [Ramsey Theory 1: A Motivating Example](https://www.youtube.com/watch?v=7p76yYMth5A)

### [Morse Theory: Lecture 1](https://www.youtube.com/watch?v=yun73TgUDyg)

### [Polya explains the problem solving technique](https://www.youtube.com/watch?v=h0gbw-Ur_do)

### [Xing Gao 9/11/15 Part 1](https://www.youtube.com/watch?v=GnYwWvuOxgA)

### [GSS Spring 2016 - Clive Newstead: Species, Structures and Stuff](https://www.youtube.com/watch?v=fGsP62E91ng)

### [Alexey Radul - Probabilistic Programming Live-code](https://www.youtube.com/watch?v=8YUUuZMawdY)

---
