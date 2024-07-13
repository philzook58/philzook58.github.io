Problem 2. {#problem-2. .unnumbered}
----------

We can show that $O'$is indeed a topology by checking each of the axioms

1.  $X\cap A=A\Rightarrow A\in O'$ ,
    $\emptyset\cap A=\emptyset\Rightarrow\emptyset\in O'$

2.  Given $Q,W\in O'$there are $U,V\in O$ such that $Q=U\cap A$ and
    $W=V\cap A$. $Q\cap W=(U\cap A)\cap(V\cap A)=(U\cap V)\cap A$. Since
    U and V were in O, so too must $U\cap V\in O$ by axiom two applied
    to $O$.

3.  Similarly given $Q_{\alpha}\in O'$there is a $U_{\alpha}\in O$ such
    that $Q_{\alpha}=U_{\alpha}\cap A$.
    $\cup_{\alpha}Q=\cup_{\alpha}(U_{\alpha}\cap A)=(\cup_{\alpha}U)\cap A$.
    Since $U_{\alpha}\in O$, so too must $\cup_{\alpha}U\in O$ by axiom
    three applied to $O$.

Problem 4.  {#problem-4. .unnumbered}
----------

1\.

1.  Since every topology on $X$ contains $X$ and $\emptyset$by axiom 1,
    the intersection of an arbitrary number of them greater than 0 will
    also contain these two sets

2.  If $U,V\in O_{X}$ then they must be in every topology R to survive
    the intersection of all R. If they are in each individual topology
    R, then each individual topology R must also contain $U\cap V$ by
    axiom 2. Since $U\cap V$ is in all R, it too will survive the
    intersection and thus $U\cap V\in O_{X}$

3.  If $U_{\alpha}\in O_{X}$ then they must be in every topology R to
    survive the intersection of all R. If they are in each individual
    topology R, then each individual topology R must also contain
    $\cup_{\alpha}U_{\alpha}$ by axiom 3. Since
    $\cup_{\alpha}U_{\alpha}$ is in all R, it too will survive the
    intersection and thus $\cup_{\alpha}U_{\alpha}\in O_{X}$

2\. $O_{X}$ contains Z because it is composed of the intersection of
topologies all of which contain Z.

3\. $O_{X}$was constructed by an intersection of all topologies that
contain Z. The result of an intersection is always of subset of any
individual set that went into the intersection. Since any topology that
contains Z went into the intersection, $O_{X}$must be a subset of that
topology.

4\. To make f continuous the topology must contain Z. $O_{X}$is a subset
of any topology that contains Z, hence it is the smallest that pulls it
off.

Problem 6. {#problem-6. .unnumbered}
----------

![image](C:/Users/Philip/Documents/Zmod3Top.png)

The hope is that since the projective plane has homotopy group $Z/2Z$,
we may adjust the two-ness to three-ness to get $Z/3Z$.

Problem 8. {#problem-8. .unnumbered}
----------

1.  Every triangular face has 3 edges associated with it. Our definition
    of a boundary-less 2-mesh states that every edge is shared by
    exactly 2 faces. Hence we are exactly double counting if we count 3
    edges for every face. $$3F=2E$$

2.  By substitution the definition of $\chi$ into 1. to remove the
    variable F we get $$3(\chi-V+E)=2E$$ $$E=3(V-\chi)$$

3.  In the case of maximal connection, every vertex is connected to
    every other vertex by an edge. We may count them by choosing each of
    V possibilities to start and edge and multiplying by $V-1$
    possibilities of vertices to connect it to. We then divide by two
    since the edges are directionless. $$E\le\frac{V(V-1)}{2}$$ We then
    may substitute in result 2. to remove E $$6(V-\chi)\le V^{2}-V$$
    $$0\le V^{2}-7V+6\chi$$ This condition may obtained in either of two
    regions by the quadratic formula
    $$V\ge\frac{1}{2}(7+\sqrt{49-24\chi})$$
    $$V\le\frac{1}{2}(7-\sqrt{49-24\chi})$$ The maximal value that may
    be obtained for the second inequality without going complex is 3.
    Since we were considering closed surfaces, which must have more
    vertices than 3, the first inequality is the one that holds.
