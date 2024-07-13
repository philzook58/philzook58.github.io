The fundamental objective of control theory is to make an output exactly
match an input.

The trouble is that the output has a mind of its own ,either due to the
natural dynamics (like holding a pendulum) or because of weird operating
charecterstics (like an audio amplifier with linear or nonlinear
distortions)

Interpolation - input is actual function. Next stage is sampler. Then
interpolation function. Then output. Feedback between smapler stage and
inteprolation stage gives regularization

Sliding interpolation window. Splines. Could still use chebyshev
polynomials even though not at cehbyshev points. Is this wahat a finite
DSP/Upsampling filtering does?

Prefiltering = regularization?

Too many differentiators (zeores) will cause instability

Z-transform. z is the shift operator like k is the differentiation
operator.

Input and output impedance

$$\left[\begin{array}{cc}
C & A\\
A^{T} & 0
\end{array}\right]\left[\begin{array}{c}
I\\
V
\end{array}\right]=\left[\begin{array}{c}
V_{0}\\
I_{0}
\end{array}\right]$$

The adjancency matrix A is a topological thing taking space of edges to
space of vertices. $A^{T}$is a coexterior derivative acting on dual
space.
