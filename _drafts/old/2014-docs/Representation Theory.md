Why should we care?

Symmettry baby.

Even and Odd can save your bacon

Selection Rules - The Wigner Eckart Theorem

Group theory QR algorithm. Cycle through group and perform the
elimination according to each member, but then flip the QR on all.
Dumbest thing you could do (that might work). Well\... actually you
could finish the QR on each (since the matrices have to be degernate).
Not sure if there is advantage to cycling instead of finishing eahc and
moving on. Maybe convergence is improved?

Find Schur form one by one. Go to submatrices and find schur form for
next member of group. That ought to do it.

Those fancy little Gauss Law tricks. The Electric field function vector
$\vec{E}\otimes f(x)\otimes f(z)\otimes f(y)$. The surface integral
would be a row vector with 0 almost everywhere except at the surface,
where it has an area vector $(\vec{dA}\otimes f(OnSurface?))^{T}$. This
is basically discrete exteriori calculus style. Dot those two suckers
together. However, we also got some symmettry goin on. We have operators
that will rotate that sucker. Basically oribtal angular momentum and
spin angular momwentum operators.

This is all about degeneracy

Spinors and clebsch gordon as a limit of some finite group? 2d roations
is limit of $C_{n}$. 3d seems tougher. Only so many regular polyhedra.
The sphere as a limit?

Groups
======

Groups are the minimal axioms that you might consider to define a set of
transfromations, or a reversible actions that you might take. You can
compound them, or undo them. The order that you perform them might
matter. And it is always possible (and easy!) to do nothing.

A more concrete example of a group is the set of $n\times n$ invertible
matrices. They transform vectors into other vectors.

Rotations or reflections of Vectors is even more specific example.

Therefore abstractly a group is a set of objects that can be combined
with the following axioms

1.  The identity E exists. $EA=AE=A$ (Do nothing)

2.  If A exists, so does $A^{-1}$. $AA^{-1}=AA^{-1}=E$

3.  If A and B are in the group, so is AB. (Closure, Two actions is
    still an action)

4.  Associativity $A(BC)=(AB)C$

Alright. That's out of the way. Anyhow

Rearrangement theorem
---------------------

The fact that every element has to be invertible means that when you let
X run through all possible elements$BX$ also runs thorugh every element
once and only once. If you repeated, then you wouldn't be able to figure
out which X you came from, hence B wouldn't be invertible.

Conjugation
-----------

Basically, in matrices, we can perform similarity transformation

$$S^{-1}AS$$

By the nature of the beast, this does not change most porperties of the
matrix, because when we matrix multiply, an S cancels an inverse S.

So the set of matrcies that are related by similarity we might call a
similarity class. They will all have same determinant and same traces.
If we assume they are diagonalizable, they have all the same eigenvalues
too. Same Jordon Canonical form, etc.

The equivalent in group theory is conjugacy and conjugacy classes.

E is in a class by itself. Since they don't have the identity, classes
are not subgroups (except for the trivial one with E in it).

Subgroups
---------

A subset of the elements in the group that satisfies the axioms of a
group is called a subgroup. Deal with it.

Lagrange Theorem

### Normal Subgroups

Normal Subgroups are a hunk of your group operators that commute with
the rest of your group. There may be many.

A big deal in group theory is trying to factorize groups (like the big
deal in number theory is factorizing into primes). Ultimately all groups
are classified

Cosets
------

Quotients

The quotient with respect to a normal subgroup is saying that two group
members are now effectively the same if they differ by only an element
of the normal subgroup.

Conjugacy classes created by conjugating with the normal subgroup.

Representations
===============

Commuting and degeneracy
------------------------

Degeneracy is a nasty unpredictable bird. It means we no longer have a
unique eigenbasis. Under perturbation, radically things can happen, like
a chicken laying an egg on a knife edge. Degeracy also carries
connotations of symmettry.

Two nondegenreate operators (matrices) can only commute if they share
the exact same eigenbasis.

Two degenerate operators can commute in interesting ways. One may stir
up the eigenbasis of the other.

HOwever, sets of commuting operators are always simulataneously
diagonalizable

Stack family of commuting matrices

$$\left[\begin{array}{c}
A\\
B\\
C
\end{array}\right]$$

Now perform SVD. Largest square eigenvalues

$$\sigma^{2}=\lambda_{A}^{2}+\lambda_{B}^{2}+\lambda_{C}^{2}$$

Picks largest overall eigevanlue, then the others break the degeneracy

Gives eigenvalues of

$$\left[\begin{array}{ccc}
A^{T} & B^{T} & C^{T}\end{array}\right]\left[\begin{array}{c}
A\\
B\\
C
\end{array}\right]=A^{T}A+B^{T}B+C^{T}C$$

I would suspect whatever I come up with is not going to be numerically
efficient.

Construction: Find one eigenvector (power method). Unitarily transform
into a biasis with this vector. Now your matrix is block upper
traingular. Go to next subblock, repeat. If you want simulataenous,
power method with A, then power with B, then power with C. Probably
highly unstable. (No guarantee the maximum eigenvector of A is also B
and C). I've heard good things about QR method. Individually diagonalize
ABC, then combine somehow. Diagonlize A. Porject B onto degenrate
subspace. Diagonlize within subspace, and so on.

Degeracies can very easily occur under direct products and direct sums.
The new eigenvalues will be simple combos of the old ones.

Schur's Lemma

If a representation is irreducible, it can't commute with jack crap
(except 0 or a constant). If it is reducible, it does. Basically, if
there is some subspace that is closed under all operations, even if it
is just a 2d subspace, that gives enough wiggle room to produce a
nontrivial commuting operator. If there is no subpsace that is closed
(representation irreducible), then there is no wiggle room.

A siple example is the porjection operator onto the reduced susbspace.

We can make an arbitray operator symmettric with respect to the group
matrices by just symmettrizing it.

However, we can explicitly construct a clever operator

$$M=\sum_{R}D(R)XD(R^{-1})$$

Where X can be anything. This M commutes with all delements of the
group, thanks to some dummy index manipulation (thanks to the
rearrangement theorem which says that summing over all R is the same as
summing over all BR since B maps one-to-one group elements, inverse
exists)

$$MD(Q)=\sum_{R}D(R)XD(R^{-1})D(Q)=\sum_{QR}D(QR)XD((QR)^{-1})=D(Q)M$$

Since X is arbitrary, we have the freedom to manipulate it.

Now what about non-commuting operators?

We can find out how many copies of an irreducible reprentation there are
in a given weird representation by taking an inner product of characters
from our character table with the traces of our weird matrices. $a_{i}$
is the number of copies of irreducible rep i. the character is a vector
in group space (has number of entries equal to degree of group).

You need an extra $g_{i}$ factor for the number of conjugacy classes.
Conjugacy classes have the same characters. You want to collect them
because otherwise, the characters won't make a complete basis. You'll
work in some conjugacy subspace of the full group space

$\chi$ vectors have one entry for each conjugacy class. There is one
$\chi$ per irreducible representation type.

$$g_{i}\chi^{(i)\dagger}\chi^{(j)}=g\delta_{ij}$$

$$\chi=\left[\begin{array}{c}
trD(R_{1})\\
trD(R_{2})\\
trD(R_{3})\\
\\
\\
\end{array}\right]$$

$$\chi=\sum a_{i}\chi^{(i)}$$

$$\chi^{(i)\dagger}\chi=ga_{i}$$

Irreducibility test: Find magnitude $|\chi|^{2}=g$. If true, then
irreducible, since only one $a_{i}$was 1.

OTHER
-----

For now representation will be sets of matrices that are homomorphic
with the group. Homomorphic means that the group multiplication doesn't
get screwed up in the matrix multpilcation. If $\pi(g)$ is the matrix
that correpsonds to the group element g, then that means

$$\pi(g_{1}g_{2})=\pi(g_{1})\pi(g_{2})$$

We can choose to either multiply the group abstractly first then find
the matrix, or find the matrices first then multiply them.

$\pi(g)$ isn't necessarily 1-1. If it is, then it is given a special
name, an isomorphism.

$$vec(\Gamma(g))$$

If we exapnd our minds a little by considering sums of the group
matrices

$$\sum_{g\in G}a_{g}\Gamma(g)$$

We see that this is in fact a linear subspace or matrecies that is
closed under matrix multiplication.

$$(\sum_{g_{1}\in G}a_{g_{1}}\Gamma(g_{1}))(\sum_{g_{2}\in G}b_{g_{2}}\Gamma(g_{2}))=(\sum_{g_{1}\in G}\sum_{g_{2}\in G}a_{g_{1}}b_{g_{2}}\Gamma(g_{1}g_{2}))=\sum_{g\in G}c_{g}\Gamma(g)$$

where $$c_{g}=\sum_{g_{1}g_{2}=g\in G}a_{g_{1}}b_{g_{2}}$$

Now, to my mind this looks like convolution. If G was a cyclic group,
that is just in fact what it would be.

How very curious.

The subspace of group matrices is the column space of the following
matrix

$$Q=\left[\begin{array}{cccc}
| & | & |\\
vec(\Gamma(g_{1})) & vec(\Gamma(g_{2})) & vec(\Gamma(g_{3}))\\
| & | & |
\end{array}\right]$$

The rows of the vec matrix are labeled by the two indices of the matrix,
and the columns are labeled by a group elements

These vectors definitely are not orthogonal

The dopt product of ovecotrized matrices is equivalent to a trace of the
matrix product of the matrices. We will use these two expression
interchangeably.

$$vec(B)^{T}vec(A)=tr(B^{T}A)$$

We see a squares matrix and we ask "What are its eigenvectors,
eigenvalues?" We see a rectangular matrix, we ask "What are its singular
vectors, singular values?"

The Grammian of a set of vectors, is the matrix composed of all the
inner products. In our case that will be a $|G|\times|G|$ (Where \|G\|
is the number of elements in the group) matrix

$$Gram=Q^{T}Q=\left[\begin{array}{cccc}
tr(\Gamma(g_{1})^{T}\Gamma(g_{1})) & tr(\Gamma(g_{2})^{T}\Gamma(g_{1}))\\
tr(\Gamma(g_{1})^{T}\Gamma(g_{2})) & tr(\Gamma(g_{2})^{T}\Gamma(g_{2}))\\
\\
\\
\end{array}\right]$$

The squares of the singular values will be the eigenvalues of the
matrix, and the euegenvaectors with be the right singular vectors.

An operator of interest is

$$A\otimes A^{-1}$$

This is exactly the matrix that coresponds the a conjugacy (or
similarity) transformation of an element in our group

In indices

$$A_{ab}A_{cd}^{-1}$$

If we contract over various indices, we get the identity (ad or bc), or
one of the original matrices back times the trace of the other one (ab
or cd).

$$$$

Block diagonalization is a generalization of eigenvalue decomposition on
the blokc level. We now have invariant subspaces which get mapped to
some scaled version of themselves instead of eigenvectors. The amount
they are "scaled" by is their diagonal block.

$$E_{1}=\left[\begin{array}{c}
\Gamma(g_{1})\\
0\\
0\\
0
\end{array}\right]$$

$$E_{2}=\left[\begin{array}{c}
0\\
\Gamma(g_{2})\\
0\\
0
\end{array}\right]$$

$$E_{i}^{\dagger}E_{j}=I\delta_{ij}$$

### Fourier

A useful decomposition

$$I=\sum_{l,R}\frac{d_{l}}{h}D^{l}(R)$$

I think this is represenation theories version of the completeness
relation

$$\sum_{n}|n><n|=I$$

The great orthogonality theorem becomes

$$<m|n>=\delta_{mn}$$

For a grid of periodic translations $e^{in\frac{j\pi}{N}}$ are the
functions/vectors of the irreducible represantions, eahc of which is one
dimensional. $D^{(j)}(T^{m})=\chi^{(j)}(T^{m})=e^{i\frac{mj\pi}{N}}$ are
the transformation matrices and characters of the jth irreducible
representation. Summing over m (the group members R), we do indeed get
orthogonality between different representations (j). This example is
confusing because different parts (matrices, characters, and functions)
look very very similar.

Fourier decomposition could be seen as projection into irreducible
subspaces using the character (or matrix).

$$c_{\alpha}f^{\alpha}=\sum_{m}\chi^{\alpha*}(T^{m})(T^{m}f)$$

Okay. so kind of screwy, since the fourier coefficient is c but we have
a real space vector $(f^{\alpha})_{n}=e^{in\frac{\alpha\pi}{N}}$

Proably the D form is a better analogy

$$c_{\alpha}f^{\alpha}=\sum_{m}D^{\alpha*}(T^{m})(T^{m}f)$$

Fourier synthesis is\...?

$$f=\sum_{\alpha}c_{\alpha}f^{\alpha}$$

That's pretty boring.

Point Groups
------------

### $C_{n}$

a rotation axis - fourier esque - each element is class by itself

### $C_{nh}$

\- rotation + reflection axis. reflection axis pierces reflection
plane.Hence the two commute. Abelian, so all memeberrs in there own
class.

### $C_{nv}$

Thoughts
--------

To mnake a computer fidn irreducible reps, build all your transformation
matrices for the group, then sequentilly find schur form

How to determine the symmettry group from the stiffness matrix?

COnsider the resolvent $(U(R)-\lambda)^{-1}$. It can be used with
contour integrals to form projection operators. Useful?

l=1 stereographic respresentation. Stacked spheres? Stacked projection
planes? l=0 has just one component. Null. Could this be projection onto
middle point that is contained inside porojection plane. Then everything
projects to 0. Clebsch gordon. two spheres stacked inside larger sphere.

crystal field theory. Why does it matter? What are the slection rules
for transitions betwene undegenrated d orbitals? COnsider a linear ionic
molecule first (although I'm not sure such a thing exists). The linear
field would break the p orbital symmetry

Algroithm for irreducible representations
-----------------------------------------

Block diagonalization is much easier than an eigenvalue problem, so this
is a dumb procedure. But nevertheless

Suppose we exatcly diagonalize A. We could also exactly diagonalize A in
the correct block irreducible form. What is the possible wiggle room in
this rep? How can an arbitrary diagonalization differ from the correct
one.

1.rotations within degenerate subspaces.

2.permutations of vectors. The other members of the gorup in this basis
might have a bunch of zeros all over the place.

First we deal with 1. Take each degennerte subspace in A, and form
matrix elemtns in B and diagonalize. If this still has degernate
subspaces, continue on to C and so on. If it makes it all the way
through: cool. Degenerate rotation must truly not matter. I thought that

To Deal with two, make a graph of the basis vectors. Put an edge on the
graph if any matrix element for those two vectors for any group member
is nonzero. Sepearte graph into clusters. Can Form adjacency matrix,
multiply it up to order of group and find nonzero elements for example.

Weights and Roots
-----------------

Lie algebras. Apparently you can extend the sum over group elemnts to an
integral over group elements.

Adjoint representation is the representation that uses the commutator
matrix elements as the matrices themselves. For SU(2) it is the 3d rep
$\epsilon_{abc}$.

Cartan Subalgebra is the maximally commuting set of generators. Not
apparent because su(2) doesn't have a set greater than 1. If one has non
degenrate eigenvalues all the others must be degenerate in those two
eigenvectors.

Their eiegenvalues are called the roots?

Kac-Moody
---------

I think these are the algebra of moments of currents or the
