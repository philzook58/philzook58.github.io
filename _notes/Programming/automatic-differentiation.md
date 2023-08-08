---
layout: post
title: Automatic Differentiation
---

See also:
- Compilers note - especially polyhedral computation section

bring your own codegen BYOC Chen 2021
halide
tvm
pytorch
ilang
egraph for equivalent _patterns_ ? no that's not what he's saying
glenside

flexasr
hlscnn
vta

im2col
tvm 
polyhedral
glesnide
tiramius?

pytorch and tensorflow have irs probably too
mxnet
apahce tvm and mxnet. Huh
glow?
https://discuss.tvm.apache.org/t/google-lasted-work-mlir-primer/1721/3
polyhedral


[The deep learning compiler a comprehensive survey](https://arxiv.org/pdf/2002.03794.pdf)
xla
ngraph
TC


Julia has its own thing going on probably
tvm
mlir

egraphs useful for finding BIG patterns
ad 
tapinade - low level imlet

[ Automatic Differentiation Handbook.](https://github.com/bob-carpenter/ad-handbook)


[Systematically Differentiating Parametric Discontinuities - gilbert](https://people.csail.mit.edu/sbangaru/projects/teg-2021/)

[A simple differentiable programming language - Abadi and plotkin](https://dl.acm.org/doi/10.1145/3371106)


micrograd
https://github.com/karpathy/micrograd

```python
class Value():
    def __init__(self, value):
        self.value = value
        self.grad = 0
        self.backward = lambda (): None
    def __add__(self,x):
        r = Value(self.value + x.value)
        def backward():
            self.grad += r.grad
            x.grad += r.grad
        r.backward = 
    def __mul__(self,x):

x = Value(2)
e = x * x
e.backward()

```