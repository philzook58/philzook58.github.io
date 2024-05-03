---
author: philzook58
comments: true
date: 2019-02-15 19:12:50+00:00
layout: post
link: https://www.philipzucker.com/?p=1291
published: false
slug: Network Coding
title: Network Coding
wordpress_id: 1291
---

https://en.wikipedia.org/wiki/Linear_network_coding




In a standard network ,you have a graph of connections and you send packets over the links.




In network coding, you send linear sums in finite fields over the links. Then if the receivers are getting from multiple sources with different linear sums, they can back out what the original messages were.




This is an extension of the original guy. Just sending some packet is sending linear combinations with only one 1 and all the other coefficients 0.




The coding advantage




There is a distinction between




 




You don't lose anything because the packet combinations are invertible.




Linear error correcting codes do something very similar.




https://en.wikipedia.org/wiki/Linear_code




In fact, I think this is the same as doing some kind of error correcting code on the combined space of all the sources. The network imposes a structural constraint on the matrix available.




https://en.wikipedia.org/wiki/Concatenated_error_correction_code




 




Galois Fields aka Finite Fields. It is remarkable that there are closed finite fields that work. The modular arithmetic over prime numbers works. It needs to be prime in order to have a multiplicative inverse I think.




The extension to polynomials with mod coefficients makes a closed finite vector space. Multiplication is modulo another polynomial




What does network coding do and not do? Comparison to packing together packets. Could mix packets by just splitting them.




Coefficient overhead.




 




 




 




 




PRISM / TLA+




reliable multicast with network coding.  CodePipe




https://ieeexplore.ieee.org/abstract/document/6714456/




Multicast network coding patent




https://patents.google.com/patent/US9537759B2/en




 




 




index coding?




 




Planar graphs - We live on 2d earth, so special results are useful.




 




 




 




What are models of network coding?




How do I model held information.




What is the simplest possible analog of what we are trying to do? Solvable versions.




 




Traditional routing:




No coefficients needed




not all or none proposition. Incrmentally get more packets.




 




Advantages of Network Coding:




SOunds good.




Less likely to send redundant packets.




 




 




Mix:




Sparsify somewhat in interior nodes. Complete sparsifcation -> traditional packets. No sparsification -> full dense network coding. Having novel mixes being generated in the interior still might get much of the benefit of network coding.




 




 




Coefficient schemes:




The coefficient will be built using a pseudorandom generator. Just send seed.




Or have fixed codebook in memory. Use seed offset. Allows random access.




Or use simple mathemtical form. Perhaps just a ramp function and seed is offset? Or some kind of linear recucrrence relation? Something that is simple enough to jump to spots.




How to combine codebooks? If you have a message fro seed A and a message from seed B with different masks how to you combine them into a new mask and a new seed? In this case the mulpticative recurrence seems nice. We can then multiply an entire vector times a constant to bring to a new seed.




But for exactly this reason these vectors are not linearly independent. The linear conguential generator is sort of the combination of these the mulpticative and the additive coefficient model.




We want closure of seeds over addition and scalar multiplication. a linear combination of the coefficients should lead to some knowable change in seeds. We need something like a homomorphism between the vector space of coefficients and something smaller (seed space).




bit mask of messages: #nodes bits if all combos equally likely.




They aren't though. Incremental changes of bitmask over time. And spatial correlation. It seems to me that a graph will have a hierarchical clustering of nodes.




Grouping: Put nodes together into clusters and only forward once you have enough to make cluster dense. This is a spatial bit mask encoding scheme. The bit mask is in sort of a quadtree form.




 




A bit mask is like using a full GF(2) coding.




Compression via run length encoding (assumes many 0s and 1s)




Is just working in GF(2) insufficent? Conventional wisdom says you need a larger space. But does not a large number of nodes also give you a big vector space to randomly scramble?




Check out cryptol in haskell. has a F(2^m) module.




* * *




Optimization of network coding networks




How to describe the objective: 




Prose: Get all the messages in and have it be reliable and fast




All messages: Coefficient matrix at hub has to be invertible




 




Different perspectives: unroll time




What is the state of the network?




CG = coding group size




If you give me the vector at each node? N_Nodes * CG values of GF2




Probablity of some vector at each node.  Very large state space.




(2^8) ^ (N_Nodes * CG) values of probability. For every N*CG GF2 assinment, we need to assin probability.




Randomness of combination means that worrying too much about specific GF2 values is silly.




If we could assume probability is independent, then N*CG*2^8 values of probability.




 




Dynamic programming?




 




One could also consider unrolling time, basically multiplying a factor of time steps times every quatity.




After unrolling, the network is naturally expressed as a probabilistic graphical model.




 




The continuum vector model. If instead of GF2 values, we use continuous vectors. It may be natural to model the distributions of these vectors as gaussians. This allows 1 layer of correlation to be described.




Correlation amongst the hub nodes is bad. We want the messages into the hubs to be maximally uncorrelated. This might be a good approximation to the solvability condition.




 




 




Instead of going probabilistic, we can instead try going trajectory optimization style. Pre pick the combination coefficients. Control variables are which channels to allow to transmit. I have not figured out how to deal with the full rank condition. Or perhaps even with the transmission requirement. SDP condition. I am not sure that the activation technique will work here.




 




 




Information Flow model.




Something that I feel seems reasonable, but makes me queasy. I don't know how to actually connect this model to what is really going on. It just feels similar. And until I have understanding of that, this is just as heuristic as genetic algorithms or neural networks.




Each source node is a source of 1 bit. Flow is conserved at each node. 




Unroll in time. Edges are activated by the rules of non collision. All temporal hub nodes can sink up to 1 bit.




Flow rules then will solve for the "informational path" that the info took from source to hub.




Unrolling all time seems like it makes the system unreasonably large.




A periodic schedule seems acceptable. Do greedy graph coloring (also gives initial feasible solution) for sufficient large period. Then O(#edges * Period) variables. Say 100,000. Well for target n_nodes = 60,000, yikes. Early stopping is available though.




Each hub node can sink up to T/P bits (total time slots divided by period). Similarly that is the new cap on information flowing through an edge.




Can heuristically tune for some good stuff. Add term to try and spread the info flow as much as possible (add cost of square of info flow). Or try to make nodes near hub to talk more by weighting activations. Or add weighted cost as to strength of links. Add cost to later hub activations vs earlier ones.




Break loops lazily? Not sure if necessary. Loops do not help info flow into hub




This model does many good things, but I'm not convinced it won't be able to send the same linear combination twice.




Might want to have flow distinguish it's mixture of individual messages. copy the network CG times.




 




 




Information. Mutual information. Correlation. Solvability. Linear independence. It is the spooky connections between nodes where information lies, not in nodes themselves. Dot product.




Edges vs nodes. Edges may be labelled with mutual information of the nodes connecting them?




 




Edges as matroids




I tthink edges are actually vertices in the matroid model? And there is a loop connecting any edges connected to a single vertex. Vertices are loops. Because thost edges can't possible be all independent.




 




Comntinous gaussian model. We probably want roughly unitary evolution. We shouldn't have been [icking random coefficients, we should have been picking a random mixing angle.




Given a fixed transmission schedule and mixing coefficients, we can schur complement out to just the hub messages. Look at their correlation (off-diagonals). Ideally should be zero.




Is there a way to keep evolution of correlation matirx linear?




 




Local but slightly lmore large optimal moves.




Consider the matroid at each time step. Dynamic programming on this?




Matroid goes from one cnentrated at information rogin vetices to one that is spread everywhere.




Maybe use GF(2) for optimization. Should perform worse that GF(2^8) but has the right flavor and is smaller. encoding multipliaction will be bad the larger the field is.




Seems more conceivable to build. Easier to express the independency clause?




What is the witness of independence. The inverse. write out inverse in Z3 persay? or determinant




crytpominisat and xor constraints




 




 




Methods of solution:




SAT




SMT




CSP




MILP




Genetic




Anneal




 




Methods of Modelling: General to more specific




Probability of full space model unrolled completely in time.




can then enforce the cyclical schedule.




can switch from probability to sample, or prbability to "infromtation"




"infromation" Flow Model




example trajectory




"Matroids"




Rollout time vs not roll out




collisionless graph coloring




Gaussian model




 




I've been focussing on the network coding and collision time stuff, but optimizing forwarding groups / coding groups is equally if not more important.




forwarding - constraint that every gorup must have path to hub. Robust path, knocking out any 1 node should not kill path if possible.




Forwardfor - indicator variable per edge. edges are knocked out if you don't forward that message.




codings groups should be clumped? Why? Mostly to reduce forwarding I think. And to quickly get the coefficients all mixed up good.




path for every one to the hub. How to express that?




Greedy : segement graph in clusters. add shortest path to hub as a forwardiug chain. Greedily thicken forwarding groups.




Salesman style. Forwading indicator variables. if forwarding, then there must be two forwarding neighbors. minimize total numebr of forwarding. Or limit total forwarding < 5. Or add signifcant cost. Make total forwarding = 5? And then add cost for anything above that. Slack vairable in inequality.




 




Kind of feels like another flow model. Coding Group flows. Coding Groups produce 78 units of flow. Hub sinks 78 units. we need to turn on forwarding for with inidcator variables, and we want to mininized the absolute value total flux in any particular edge (as a hueristic for spreading the information around). there is a ratio of how much forwarding for costs vs how robusat we want to be. Multi vlaue objective. We could also make which coding gorup is which variable by giving each node indicators about where we want thir source to come from.




N_Nodes * coding_group binary variables. ~ N_Nodes **2 / 78 variables




Symmetry breaking?




The problem instances are just too large. It is useful to consider an all inlcusive model, but yeah, we may need to break it up into pieces.




Either stages of alternating the different problems. Or perhaps doing a single linear solve and just taking greedy suggestions. Hot start may help.




The first step is to express ourselves as cleanly as possible. 100 node graphs should be doable.




All inclusive flow model: Unroll for coloring window, flow with collision constraint and forwarding constraint.




Conding gorups are force to forward for themselves.




iteration. optimize forwarding group, optimize schedule




 




Graph color (everyone talks once) + add greedy colors (there may be other moments one can talk). send bit mask schedule. Could just fix total colors at 64 or something. Then greedily schedule.  Still would want greedy grpah coloring just to be sure everyone is talking once.




Then figure out the grouping / forwarding.




clustered groups? radial groups? minimize inter group distance? minimize intergroup + hub distance?




Pick farghests node from hub. This is group 1. put all nearest neighbors into that group. iterate.




It is possible that you are still forwarding for a group that you have solved for.




Once we have coding gorups picked, we oculd pick forwardinf for with a newtork flow problem. Add a cost to flow. Absolute value with a kink at 5 or negative 5/   78/5 . This will tend to make a sparse solution. Then use that value for the next coding group. Stuff that already has a high cost should probably also have a high cost.




Or rather maybe do this whole thing as an LP. all coding gorups at once. With each edge have coding groups different flows on it.




Mostly the judgement of coding group selection is the ultimate forrwarding for cost. So could try different methods and take best one with respect to that cost. no cost associated with intra coding group flow?




A very reasonable way to do forwarding.




Forwarding using absolute value + quadratic cost. ratio is sparsity vs spreading. Then add binary variables for group belongment. Could iterativley ask for group belongment. Symmettry breaks the thing. Pick some special node and then zero or one whther you belong to the same gourp as him. sum of all = 78. Then fix those and pick a new unsued node and do the same. Heurstical, but reasonable.




 




weighted graph multi-coloring according to flow value. we want important nodes to get more colors. #timeslots in microschedule * N-Nodes variables. Constraints from augemented graph.




 




maybe forwarders shouldn't mix? seems dangerous?




What are the odds that a random GF(2^8) matrix is singular? pretty small.




Jeff's suggestion that maybe forwarding nodes should only transmit forward. Adds a little complexity.




 




The hub pulsing out Group n solved could be a big win. Avoids continued forwarding and coding. Since inner layers are very likely to solve earlier.




Maybe forwarding gruops should maintain one slot just for the most recently heard thing that isn't one of their forwarding groups?




 




ditributed collision avoidance. randomly with 1/10 chance during a schedule window. Don't transmit and just listen.




 




 




 




 




 




 








