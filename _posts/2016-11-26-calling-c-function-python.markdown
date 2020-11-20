---
author: philzook58
comments: true
date: 2016-11-26 02:42:11+00:00
layout: post
link: https://www.philipzucker.com/calling-c-function-python/
slug: calling-c-function-python
title: Calling a C function from Python
wordpress_id: 574
---

I'm working on piping together numpy and a gpu accelerated FFT on the raspberry pi.

[http://www.aholme.co.uk/GPU_FFT/Main.htm](http://www.aholme.co.uk/GPU_FFT/Main.htm)

I've never done anything like this.  This is very useful.

[http://www.scipy-lectures.org/advanced/interfacing_with_c/interfacing_with_c.html](http://www.scipy-lectures.org/advanced/interfacing_with_c/interfacing_with_c.html)

The official docs are less useful. Maybe once you already know what's going on.

    
    #include <Python.h>
    
    
    static PyObject *squarefun(PyObject *self, PyObject *args)
    {
        int val;
    
        if (!PyArg_ParseTuple(args, "i", &val))
            return NULL;
        int sq = val * val;
        return Py_BuildValue("i", sq);
    }
    
    
    static PyMethodDef SquareMethods[] = {
    
        {"squarefun",  squarefun, METH_VARARGS,
         "Sqaure the integer given"},
    
        {NULL, NULL, 0, NULL}        /* Sentinel */
    };
    
    
    PyMODINIT_FUNC initsquare(void)
    {
        (void) Py_InitModule("square", SquareMethods);
    }


This is the basic code needed to make a squaring function callable from python. It's in a file square.c. You need that initsquare function which is called when you import. You need to list your available functions in that SquareMethods thing. And you need to extract and rebuild python style formats using the built in macros.

put this in setup.py

    
    from distutils.core import setup, Extension
    
    #RUN the following to build project
    #python setup.py build_ext --inplace
    
    # define the extension module
    square_module = Extension('square', sources=['square.c'])
    
    # run the setup
    setup(ext_modules=[square_module])


Next, I gotta figure out how to get arrays

[https://docs.scipy.org/doc/numpy/reference/c-api.dtype.html#c-type-names](https://docs.scipy.org/doc/numpy/reference/c-api.dtype.html#c-type-names)

[https://docs.scipy.org/doc/numpy/reference/c-api.types-and-structures.html](https://docs.scipy.org/doc/numpy/reference/c-api.types-and-structures.html)

These actually are pretty useful

    
    #include <Python.h>
    #include <numpy/arrayobject.h>
    
    
    
    static PyObject* square_func_np(PyObject* self, PyObject* args)
    {
    
        PyArrayObject *in_array;
        PyObject      *out_array;
    
        /*  parse single numpy array argument */
        // 
        if (!PyArg_ParseTuple(args, "O!", &PyArray_Type, &in_array))
            return NULL;
        // only accept complex 64 = 2 * float32
        if(PyArray_TYPE(in_array) != NPY_COMPLEX64){
            printf("Not a complex64");
            return NULL;
        }
    //Size of 0th dimension of array
        npy_intp size = PyArray_DIM(in_array, 0);
        
        printf("in the ole functiony poo");
        printf("array size %d \n",size);
    // pointer to a straight up c array. SHould check for c contiguous flag
        npy_float* data  = (npy_float*)PyArray_DATA(in_array);
      
        for(npy_intp i = 0; i < size ; i++){
            printf("%f %f\n", data[2*i],data[2*i +1]);
        }
    
        /*  construct the output array, like the input array */
        out_array = PyArray_NewLikeArray(in_array, NPY_ANYORDER, NULL, 0);
        if (out_array == NULL)
            return NULL;
    
        Py_INCREF(out_array);
        return out_array;
    
        /*  in case bad things happen */
        fail:
            Py_XDECREF(out_array);
            return NULL;
    }
    
    /*  define functions in module */
    static PyMethodDef SquareMethods[] =
    {
         {"square_func_np", square_func_np, METH_VARARGS,
             "evaluate the cosine on a numpy array"},
         {NULL, NULL, 0, NULL}
    };
    
    /* module initialization */
    PyMODINIT_FUNC
    initarray_square(void)
    {
         (void) Py_InitModule("array_square", SquareMethods);
         /* IMPORTANT: this must be called */
         import_array();
    }




Here is some basic garbage mostly copied from those advanced scipy notes above. I cut out out the iterator stuff. That is probably the way you'd usually want to do things. However, ultimately, I'll be able to handoff the input and output array pointer to gpu_fft. I think it is in the right format.

The way I'm currently structuring things I'm probably not going to hold your hand. Unless I withhold access to the raw C file from an intermediate python library module?

But not today. Maybe tomorrow.


