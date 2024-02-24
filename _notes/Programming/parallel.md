---
layout: post
title: Parallelism
---

See also:

- performance
- algorithms
- concurrency

[Umut Acar](https://www.umut-acar.org/home-page)
[Parallel Computing: Theory and Practice Intro in C++](https://www.cs.cmu.edu/afs/cs/academic/class/15210-f15/www/tapp.html)
[8  Oregon Programming Languages Summer School parallel algorithms](https://www.youtube.com/watch?v=8ZeGs5SBOFU&t=507s&ab_channel=OPLSS)
[sam westwick](https://www.cs.cmu.edu/~swestric/) mpl "maple" a parallel ml compiler

Disentangling

<https://enccs.github.io/gpu-programming/#> gpu programming when why how

# GPU

Why
Roofline model
latency vs bandwidth
arithmetic intensity

## Cuda

tensor cores

<https://developer.nvidia.com/blog/easy-introduction-cuda-c-and-c/>

<https://docs.nvidia.com/cuda/> docs
`nvcc` compiler `-gencode` `-arch`. godbolt nvvm nvtx
nvdisasm nvprune cuda-gdb
cudafe++ - sperates host code from gpu
cuobjdump nvprof nvlink ptxas bin2c

```bash
#nvcc
cd /usr/local/cuda-12.3/bin/
ls
#./nvcc --help

```

nvvm ir <https://docs.nvidia.com/cuda/nvvm-ir-spec/index.html> llvm ir variant
<https://developer.nvidia.com/cupti> cupti cude profiling tool interface.
<https://developer.nvidia.com/nvidia-visual-profiler> visual profiler. libnvvp
<https://developer.nvidia.com/nsight-systems> performance analysis tool

<https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#c-language-extensions> C extensions
`<<< >>>` execution configurqation. It transpiles to cuda runtime calls

PTX <https://docs.nvidia.com/cuda/inline-ptx-assembly/index.html> virtual instruction set. JITed by driver
<https://github.com/cloudcores/CuAssembler> isa changes between cards (sm_86, sm_80, sm_75, sm_70, sm_60)
<https://github.com/Danil6969/Ghidra-Nvidia-GPU> ghidra spec for one gpu. not very complete looking
<https://arxiv.org/abs/2301.11389> A Symbolic Emulator for Shuffle Synthesis on the NVIDIA PTX Code

runtime cudart.a libcudart.so
`cudaInitDevice()` `cudaSetDevice()` `cudaMalloc` `cudaFree`

thrust <https://github.com/NVIDIA/thrust>
cub
<https://github.com/NVIDIA/cccl> cuda core lbraries

<https://github.com/cuda-mode/resource-stream>
<https://github.com/cuda-mode/lectures/>
numba has cuda simulator

<https://github.com/openai/triton> triton
jax
torch.compile

cudnn
physx
tensorrt
cublas curand cufft cusolver cusparse
npp nvidia perfroamcne primitives
nvml management library
cudart - runtme
nvrtc runtime compilation
cutlass
<https://github.com/NVIDIA/cuCollections> (cuco)

book - programming massively parallel processors <https://www.amazon.com/Programming-Massively-Parallel-Processors-Hands-dp-0323912311/dp/0323912311/>

pycuda <https://documen.tician.de/pycuda/>

<https://github.com/inducer/loopy>  A code generator for array-based code on CPUs and GPUs

```python
import pycuda

```

<https://github.com/rapidsai/cudf> gpu dataframe
<https://github.com/rapidsai>

## opencl

<https://developer.nvidia.com/opencl>

<https://documen.tician.de/pyopencl/> pyopencl

<https://github.com/intel/compute-runtime> for my integrated graphics.
<https://github.com/intel/gmmlib> graphics memory management library

create context, create queue, create buffer, create program, create kernel, set arguments, enqueue kernel, enqueue copy, enqueue map, release

```python
import numpy as np
import pyopencl as cl

a_np = np.random.rand(50000).astype(np.float32)
b_np = np.random.rand(50000).astype(np.float32)

ctx = cl.create_some_context()
queue = cl.CommandQueue(ctx)

mf = cl.mem_flags
a_g = cl.Buffer(ctx, mf.READ_ONLY | mf.COPY_HOST_PTR, hostbuf=a_np)
b_g = cl.Buffer(ctx, mf.READ_ONLY | mf.COPY_HOST_PTR, hostbuf=b_np)

prg = cl.Program(ctx, """
__kernel void sum(
    __global const float *a_g, __global const float *b_g, __global float *res_g)
{
  int gid = get_global_id(0);
  res_g[gid] = a_g[gid] + b_g[gid];
}
""").build()

res_g = cl.Buffer(ctx, mf.WRITE_ONLY, a_np.nbytes)
knl = prg.sum  # Use this Kernel object for repeated calls
knl(queue, a_np.shape, None, a_g, b_g, res_g)

res_np = np.empty_like(a_np)
cl.enqueue_copy(queue, res_np, res_g)

# Check on CPU with Numpy:
print(res_np - (a_np + b_np))
print(np.linalg.norm(res_np - (a_np + b_np)))
assert np.allclose(res_np, a_np + b_np)
```

<https://github.com/KhronosGroup/OpenCL-Guide/tree/main>
<https://github.com/KhronosGroup/OpenCL-Guide/blob/main/chapters/getting_started_linux.md>

```
sudo apt install opencl-headers ocl-icd-opencl-dev -y
```

```bash
echo "
// C standard includes
#include <stdio.h>

// OpenCL includes
#include <CL/cl.h>

int main()
{
    cl_int CL_err = CL_SUCCESS;
    cl_uint numPlatforms = 0;

    CL_err = clGetPlatformIDs( 0, NULL, &numPlatforms );

    if (CL_err == CL_SUCCESS)
        printf(\"%u platform(s) found\n\", numPlatforms);
    else
        printf(\"clGetPlatformIDs(%i)\n\", CL_err);

    return 0;
}
" > /tmp/test.c
gcc -Wall -Wextra -D CL_TARGET_OPENCL_VERSION=300  /tmp/test.c -o /tmp/test -lOpenCL 
# -std=c++11 -lOpenCL /tmp/test.cpp -o /tmp/test
/tmp/test
```

<https://github.com/boostorg/compute>

<https://github.com/KhronosGroup/OpenCL-TTL> tensor tiling library

<https://github.com/ProjectPhysX/FluidX3D> fluid lattice botzlamnn
<https://github.com/pypr/pysph> Smoothed Particle Hydrodynamics (

<https://github.com/Polytonic/Chlorine> opencl wrapper "dead simple"

## HIP

## SYCL

<https://github.com/triSYCL/triSYCL>

## WebGPU

<https://developer.mozilla.org/en-US/docs/Web/API/WebGPU_API>

## Vulkan

<https://github.com/google/clspv> opencl to vulkan compiler

## SPIR-V

## Metal

# Algorithms

Parallel Scan
Sort
Reduce
parallel hashmap

# PL

TACO <https://github.com/tensor-compiler/taco>
<https://github.com/manya-bansal/mosaic>
TVM
halide

accelerate
repa
futhark <https://github.com/diku-dk/futhark>
co-dfns <https://github.com/Co-dfns/Co-dfns>

grobner gpu
datalog gpu
hvm <https://news.ycombinator.com/item?id=37805759>
sat  <https://link.springer.com/article/10.1007/s10703-023-00432-z> inprocessing <https://www.worldscientific.com/doi/10.1142/9789811223334_0178> 3sat cuda  <https://github.com/muhos/ParaFROST> <https://github.com/muhos/gpu4bmc>
resolution?
term rewriting (the was that K/J webpage)

fluids
molecular dynamics
bioinformatics
structure from motion
CT scan something
rendering

a grid of sho?
celullar automata
