---
author: philzook58
comments: true
date: 2019-02-27 17:45:36+00:00
layout: post
link: https://www.philipzucker.com/?p=1852
published: false
slug: Notes on Succinct Data Structure
title: Notes on Succinct Data Structure
wordpress_id: 1852
---




[https://www.youtube.com/watch?v=9MKEmNNJgFc](https://www.youtube.com/watch?v=9MKEmNNJgFc)







[https://haskell-works.github.io/](https://haskell-works.github.io/)







[https://en.wikipedia.org/wiki/Succinct_data_structure](https://en.wikipedia.org/wiki/Succinct_data_structure)







Ed Kmett giving a spiel







Implicit = constant overhead







Succinct = under linear overhead







Compact = linear overhead







Placing the heap data structure (a fully balanced tree) into an array is similar in flavor. We know exactly where everything is without following pointers. Implicit indexing  








Rank(i) = counts the number of nonzeros in a bit string to the left of position i 







Select(j) = Kind of the opposite of rank - Gives index where the rank first becomes j



















Forms an Adjunction in categories.







There is a category of indices and a category of bit counts. They are both preorders with an inequality.







F -| G 







F a -> b   iso to  a -> G b







arrow -> and (,) are adjucntion via currying







They make the state monad and store comonad







Hask^op.  (a -> e) <- b ~~ b -> (a -> e)







a -> (b -> e)







(_ -> e) is adjoint to (_ -> e) via flip







Interesting notation <-







Wavelet Trees.  https://en.wikipedia.org/wiki/Wavelet_Tree













[http://www.cs.cmu.edu/~dongz/papers/poppy.pdf](http://www.cs.cmu.edu/~dongz/papers/poppy.pdf)







Poppy paper?







[https://github.com/ekmett/vr/blob/master/shaders/poppy.glsl](https://github.com/ekmett/vr/blob/master/shaders/poppy.glsl)







In shader form. Ed Kmett is nuts







https://github.com/ekmett/succinct







https://directtovideo.wordpress.com/  








DFUDS LOUDS - Depth First Unary Degree sequence, level-ordered unary degree sequence 







[https://users.dcc.uchile.cl/~gnavarro/ps/alenex10.pdf](https://users.dcc.uchile.cl/~gnavarro/ps/alenex10.pdf)







Can have bitmap of interesting locations stored in small space and quickly searchable. Useful for finding brackets in a text file (shape vs data) or places where a rendered needs to update more







[https://en.wikipedia.org/wiki/Fractal_tree_index](https://en.wikipedia.org/wiki/Fractal_tree_index)








https://people.csail.mit.edu/mip/papers/succinct/succinct.pdf








Erik Demaine student 







Mihai Patrascu. Died of brain cancer age 29. Jesus.







Personal Question: Relation to BDD?







Relation to sparse linear algebra?








https://www.youtube.com/playlist?list=PLgKuh-lKre13d6vkwc3NrEh2YguAe-XLV








[https://www.youtube.com/watch?v=EVP_xLILirs](https://www.youtube.com/watch?v=EVP_xLILirs)







Python talk on PySDSL python bindings to a c++ succinct data structure library









