---
author: philzook58
comments: true
date: 2017-08-17 19:57:11+00:00
layout: post
link: https://www.philipzucker.com/?p=781
published: false
slug: Notes on Shor's Algo
title: Notes on Shor's Algo
wordpress_id: 781
---

Number theory makes me uncomfortable.

Prime factoring and Period Finding are roughly equivalent problems. That is a fact from number theory that is not so obvious, having a poor number theory background.

But then Period finding being solvable by a Fourier transform is straightforward. A fourier transform occurring in the amplitudes of a quantum wavefunction is also not so strange.

Every number can be decomposed into a multiple  of primes. This is a powerful but difficult decomposition.

gcd - greatest common divisor. For instance gcd(20,30)=10  Fast thanks to Euclid's algorithm. The largest common factor. Will be the product of shared primes. 20 = 5*2*2 and 30=5*3*2.

relatively prime - two numbers share no prime factors, equivalent to gcd=1. Which is nice because it is easy to check. Why care? Well, it is a fact about two numbers that is easy to check. The product of two numbers that are relatively prime to a third is still relatively prime to the third because it will still have no shared prime factors. 15 and 8 are relatively prime.

Totient function - number of relatively prime numbers less than itself.

Modular arithmetic - any numbers that differ by an integer number of the modulus are considered equivalent.



Hadamard Gate - All hadamard gates being applied turns a |00000> qubit state into a superposition of all possible bit strings. This is a useful step to start achieving parralelism.

Measurement - Allows the restriction of sums, filtering the state down.

Period finding - This is a use case of a fourier transform. You use the fourier transform to find the dominant period of a function.

The quantum Fourier transform. Quantum functions exhibit a kind of parrallism, but a parallelism that can't be totally accessed. You only get one result when you perform a measurement, hence destroying the total parallelism that might be in the wavefunction. Hence they represent an in between point of power between massive parallelism and doing one thing at a time (although I do not believe that this statement is actually proven, it is what people think is true).

The quantum fourier transform let's you perform a massive fourier transform, except you do not get the full spectrum back.

The QFT has the clever divide and conquer shape of the classical FFT except implemented using quantum operators.



Filtering via inteference



http://www.scottaaronson.com/blog/?p=208

http://math.nist.gov/quantum/zoo/



continued fraction analysis
