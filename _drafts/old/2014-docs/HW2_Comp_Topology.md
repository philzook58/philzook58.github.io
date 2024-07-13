1a)

The faces are described by the vectors

$$a=\alpha_{3}e_{3}+\alpha_{4}e_{4}+\alpha_{5}e_{5}$$

$$b=\beta_{1}e_{1}+\beta_{2}e_{2}+\beta_{4}e_{4}$$

subject to the constraints on the coefficients

$$\alpha_{3}+\alpha_{4}+\alpha_{5}=1$$

$$\beta_{1}+\beta_{2}+\beta_{4}=1$$ and the condition that every
individual coefficient is nonnegative

The projection on the unit vector u is defined as

$$P_{u}(a)=a-(u\cdot a)u$$

$$P_{u}(b)=b-(u\cdot b)b$$

We desire the direction u that project a and b onto the same point

$$P_{u}(a)=P_{u}(b)$$

Rearranging and using linearity of projection
$$P_{u}(a)-P_{u}(b)=0=P_{u}(a-b)$$

Hence u must be a multiple of a-b

$$a-b=u((a-b)\cdot u)=\gamma u$$

$$a-b=\alpha_{3}e_{3}+(\alpha_{4}-\beta_{4})e_{4}+\alpha_{5}e_{5}-\beta_{1}e_{1}-\beta_{2}e_{2}$$

A definition of n linearly independent vectors $v_{i}$ is

$$\sum_{i}^{n}\eta_{i}v_{i}=0$$

only if all $\eta_{i}$are 0

Our description of a-b does not yet have independent coefficients due to
the summation constraint.

$$\alpha_{3}+\alpha_{4}+\alpha_{5}-\beta_{1}-\beta_{2}-\beta_{4}=0$$

We can use this single constraint to remove $\alpha_{4}-\beta_{4}$in
terms of the other variables

$$a-b=\alpha_{3}e_{3}+(\beta_{1}+\beta_{2}-\alpha_{3}-\alpha_{5})e_{4}+\alpha_{5}e_{5}-\beta_{1}e_{1}-\beta_{2}e_{2}$$

$$=\alpha_{3}(e_{3}-e_{4})+\alpha_{5}(e_{5}-e_{4})+\beta_{1}(e_{4}-e_{1})+\beta_{2}(e_{2}-e_{4})$$

This expression cannot be zero unless all the coefficients are zero,
since each one contains a unique instance of particular basis vector, so
we have a set of 4 independent vectors and thus u lies in a 4
dimensional subspace

1b)

If q is the number of vertices shared, then the size of B is

$$B=(n+1)+(n+1-q)=2n+2-q$$

The bad subspace of u is still all possible $a-b$ and we still have the
single constraint connecting the coefficients, reducing the possible
dimension of u by 1

$$\sum_{i}^{n+1}\alpha_{i}-\beta_{i}=0$$

This suggests that the dimension of bad u will be

$$2n+1-q$$

2\)

If the simplices share no vertices, the size of bad u is 2n+1. Assuming
something akin to a uniform distribution, the odds of picking a point in
a subvolume is proportional to the ratio of the subvolume to total
volume in some sense. A lower dimensional subspace has 0 volume, so the
odds of picking a point in it at random is also 0.
