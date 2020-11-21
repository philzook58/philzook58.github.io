---
author: philzook58
comments: true
date: 2015-07-28 18:54:17+00:00
layout: post
link: https://www.philipzucker.com/aws-and-computing-clusters-and-mpi/
slug: aws-and-computing-clusters-and-mpi
title: AWS and Computing Clusters and MPI
wordpress_id: 79
---

Just been curious about parallel computation. Clusters. Gives me a little nerd hard-on.

Working my way up to running some stuff on AWS (Amazon Web Services).

So I've been goofing around with mpi. Mpi (message passing interface) is sort of an instant messager for programs to pass around data . It's got some convenient functions but its mostly pretty low level.

I'll jot some fast and incomplete notes and examples

Tried to install mpi4py.

sudo pip install mpi4py

but it failed, first had to install openmpi

To install on Mac I had to follow these instructions [here](https://wiki.helsinki.fi/display/HUGG/Installing+Open+MPI+on+Mac+OS+X). Took about 10 minutes to compile

so mpi4py

give this code a run

```
#mpirun -np 3 python helloworld.py
from mpi4py import MPI
comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()
name = MPI.Get_processor_name()
print "Hello. This is rank " + str(rank) + " of " + str(size) + " on processor " + name`
```
the command mpirun runs a couple instances. You know which instance you are by checking the rank number which in this case is 0 through 2.

Typically rank 0 is some kind of master

lower case methods in mpi4py work kind of like how you'd expect.  You can communicate between with comm.send and comm.recv

```
#mpirun -np 2 python helloworld.py
from mpi4py import MPI
comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()
name = MPI.Get_processor_name()

if rank == 0:
comm.send("fred",dest=1)
else:
counter = comm.recv(source=0)
print counter
```

However I think the these are toy methods. Apparently they use pickle (python's fast and dirty file storage library) in the background. On the other hand, maybe since you're writing in python anyhow, you don't need the ultimate in performance and just want things to be easy. On the third hand, why are you doing parallel programming if you want things to be easy? On the fourth hand, maybe you

The capital letter mpi functions are the ones that are better, but they are not pythony. They are direct translations of the C api which uses no returns values. Instead you pass along pointers to the variables you want to be filled.
```
from mpi4py import MPI
import numpy as np
comm = MPI.COMM_WORLD
rank = comm.Get_rank()
size = comm.Get_size()
name = MPI.Get_processor_name()

nprank = np.array(float(rank))
result = np.zeros(1)
comm.Reduce(nprank, result, op=MPI.SUM, root=0)

if rank == 0:
print result
```
