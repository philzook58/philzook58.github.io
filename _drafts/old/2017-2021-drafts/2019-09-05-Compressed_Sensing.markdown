---
author: philzook58
comments: true
date: 2019-09-05 03:33:16+00:00
layout: post
link: https://www.philipzucker.com/?p=2301
published: false
slug: Compressed Sensing
title: Compressed Sensing
wordpress_id: 2301
---




I recently heard about an interesting application of compressed sensing







The l0 norm is what we really want. But l0 is not convex







The l1 norm has a tendency to push things entirely 0. This is a very important heuristic fact. It gives a good heuristic to produce sparsity







Ill posed problems do not have a unique solution. You can tie break them with a regularizer, which are computationally useful devices to make one solution better than the other.







One common one is Tikhonov regularization







Compressed sensing takes measurements in a random basis. Odds are this basis is not linearly dependent and odds are it isn't orthogonal to the supposed sparse basis.







If a signal is sparse in some basis, in principal it feels natural that there is less information content necessary  








We know the signal is sparse, but not necessarily in which particular basis vectors. If we knew exactly wich ones it would just be a linear problem







Take full measurement, compress, store. Why not just compress in the measurement?







In order to do compressed sensing, we need to know what the sparse basis is.







Examples of compressed sensing







  * The 1 pixel camera
  * 





[https://www.raeng.org.uk/publications/other/candes-presentation-frontiers-of-engineering](https://www.raeng.org.uk/publications/other/candes-presentation-frontiers-of-engineering)







[https://pythonhosted.org/pycompsense/](https://pythonhosted.org/pycompsense/)







Connection to [https://docs.scipy.org/doc/scipy/reference/linalg.interpolative.html#module-scipy.linalg.interpolative](https://docs.scipy.org/doc/scipy/reference/linalg.interpolative.html#module-scipy.linalg.interpolative) interpolative decomposition







Can I combine 2 images with random masks and recover the originals?



