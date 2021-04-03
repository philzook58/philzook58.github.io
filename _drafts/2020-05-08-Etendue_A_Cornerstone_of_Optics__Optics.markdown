---
author: philzook58
comments: true
date: 2020-05-08 04:11:11+00:00
layout: post
link: https://www.philipzucker.com/?p=1949
published: false
slug: 'Etendue: A Cornerstone of Optics / Optics'
title: 'Etendue: A Cornerstone of Optics / Optics'
wordpress_id: 1949
---

https://what-if.xkcd.com/145/

Talking with Ben: What is the right verbiage to use when discussing etendue? How does etendue compose? I sometimes want to use the formula AA/R^2. But this is probably not quite right. Really dAdOmega is the proper one. Consider the etendue going across a surface, Snell's law style. There isn't really an A A to consider. But the pencils of rays change their acuteness going across the surface.  Why can't we heat something up with a mirror or lens to hotter than the surface of the sun? What fails in the thin lens equation? The thin lens equation seems to be saying that we could bring the focal length to 0

It does appear that the thin lens equation goes out of it's domain of applicability.

Assume conservation of etendue. Then the etendue of the light entering the lens is $latex A_{lens] \Omega_{sun} $. 

$latex \Omega_{sun} = \pi r**2 / R ** 2$

The power density at the lens is $latex \sigma_{lens} = \sigma_{sun} \frac {4 \pi r**2} / {4 \pi R**2} $. The total power entering the lens is  $latex P = A_{lens} \sigma_{lens}=A_{lens} \sigma_{sun} r**2 / R**2  = \sigma_{sun} A_{lens} \Omega_{sun} / \pi = \sigma E / \pi $.

$latex \pi  P / \sigma =  A_{lens} \Omega_{sun} = A_{spot} \Omega_{lens} \lte A_{spot} 2 \pi $

$latex \sigma_{spot} =P / A_{spot} <= \sigma_{sun} $. In other words the power density is less than the power density coming off the sun 

Etendue is conserved in Snell's law. Across a surface, the area of the beam does not change. Considering a small patch of rays the etendue of this bundle of rays upon the surface is $latex dA cos(\theta) d\Omega n_1^2$ 

Snell's law is $latex n_1 sin(\theta_1) = n_2 sin(\theta_2)$. It keeps $latex \phi_1 = \phi_2 $.  Differentiating this gives $latex d\theta_1 n_1 cos(\theta_1) = d\theta_2 n_2 cos(\theta_2)$

The formula for differential solid angle in terms of the polar angles $latex d\Omega = d\theta d\phi sin(\theta) $.

Hence $latex d\Omega cos(\theta_1) n_1^2 =    d\Omega_2 cos(\theta_2) n_2^2$

Continous changes in the index of refraction can be modelled as many small applications of snell's law, do the law of etendue also applies in this case.

Even more simply, etendue of light bundles is conserved by reflecting from a mirror.

By patching together these individual problems we get an inifitesimal picture of most of the changes we consider light going through. 

Other names Geometrical Extent. Ray volume.

Non-imaging optics

Give a concrete example that shows that etendue is diffraction.

From one perspective, the reason you can't see diffraction patterns through small holes is because what you're seeing is a convolution of the diffraction pattern over the entire source.

Etendue through a window, ~ minimun is the composition

Etendue and entropy

Optics talk. Optical combs. 

Paraxial optics and the schrodinger equations. Use sympy to derive this and fourier optics. \nabla^2 e^iS(x,y,z), but the derivative with respect to z is much larger than the others. Or, psi(x,t)e^ikz^i imega t, where we just factor out the big e^ikz factor. Marcuse boook

Validated DFT vs FT. How good is the DFT doing. Interesting from a conceptual stand point. Briggs and van Emden The DFT book. We need an iterative method of defining the dft?

Cittert van Zernike.

Sommerfeld disc example. Etendue gives better intuition for near field diffraction.

I think that the concept of etendue is vastly underappreciated. It is perhaps the fundamental principle of optics. 

[https://en.wikipedia.org/wiki/Etendue](https://en.wikipedia.org/wiki/Etendue)

Etendue is the natural volume of state space for rays of light. A ray has both position and direction. Etendue is the product of an area element $latex dA $ and the spherical angle element $latex d\Omega$. Another way avoids talking about angles at all. Etendue is the product of the differential areas of the source and target of the the light is heading from and to projected on the direction the ray is headed. $latex \frac{dA dA}{R^2}. A bundle of rays preserves Etendue as it flows. If it gets more diffuse in area, it gets more concentrated in angle.

The state of a ray is not only the position it currently is at. It is also the direction it is heading. If you want to talk about a density or intensity of rays, it needs to be a function of both position and direction. When you want to integrate this distribution, you need to integrate it with respect to a volume element that includes both the positional volume dx and the directional volume dp.

One example I like to think about is the light spreading out from the sun. It is an example so simple, it will not be mentioned in an optics course. The sun is a source of finite size. At any particular point, there is light coming from all points of the surface of the sun nearest you. When an observation point is close to the sun, the ray from one edge of the sun has quite a different direction than the ray from the opposite side of the sun. When you are far from the sun, the direction of the two rays are more closely aligned. This corresponds to the fact that the sun looks small to you when you are far away. It's angular diameter is decreased. The total amount of energy is the same on inner and outer spheres. 

![](http://philzucker2.nfshost.com/wp-content/uploads/2019/04/a9493e42-6a38-47b6-aacf-9e392b59417f-1-1-1024x881.png)

![](http://philzucker2.nfshost.com/wp-content/uploads/2019/04/a9493e42-6a38-47b6-aacf-9e392b59417f-1-1024x186.png)

The angle $latex \alpha ~ r/R_1$ and $\beta ~ r/R_2$. In terms of solid angle, this is $latex \pi r^2/R_1^2$ and $latex \pi r^2/R_2^2$

The total area that the light is diffused over is $latex 4\pi R_1^2$ and $latex 4\pi R_2^2$.  

The product of these factors is $latex \pi r^2/R_1^2 4\pi R_1^2= \pi r^2/R_2^2 4\pi R_2^2=4 \pi^2 r^2$, a constant.

Optics is first taught by describing how rays coming out of point sources are manipulated by thin lens and mirrors. The previous calculation crucially relies on the finite size of the sun.

Thinking in terms of point sources is already incorrect. A point source does not exist and the concept can lead to nonsensical or paradoxical conclusions. Every source should be considered as an area, albeit a very small one. 

Etendue also should have a factor of the index of refraction. Immediately after an interface, the area is the same on both sides, but by snell's law the angular spread del sin theta changes by a factor Of the index of refraction.

With these two examples, we've covered a majority of what light does in classical optics. It goes through changing index of refractions and it free space propagates.  

It also reflects.

  
Etendue despite being so geometrical tells you a great deal where the boundary of classical optics and wave optics lies. This transition is highly related to the transition between classical and quantum mechanics, which is generally better understood intuitively despite being so much conceptually strange. This is probably due to the availability of good pedagogy.  
  

In Classical mechanics (F= ma and all that) , talking about only position and not velocity means you are missing the point. The relevant "space" analogous to etendue of mechanics is known as phase space, the combination of both position and momentum. It has the interesting quality that volume of phase space is conserved, a result known as Liouville's theorem. This fact lies at the core of the physical meaning of phase space volume, which shows up in statistical mechanics as entropy and   

  
Numerical aperture is define as n sin theta where theta is the angular spread at the focal point. People talk about numerical aperture as.

Energy is conserved. The intensity of light per unit area goes down as R2. However at the same time the sun subtends a smaller spherical angle. Spherical angle is defined as the dA/R2. The area of the sun is constant. Hence the product of the total area of the outgoing sphere and the solid angle us tended by the sun remain constant. The intensity of light in etendue phase space stays constant. The spherical geometry makes it easy to calculate the geometrical intensity as E/A. What is happening is as the light travels outward it is spreading in area while concentrating in angle.

Etendue as expressed so far has units of m2. It can be naturally non dimensionalized by the wavelength of the light involved. When etendue is of the order Of 1 ish, one should expect to get wave effects.

Numerical aperture is a topic that is naturally understood in terms of etendue. For telescope and microscope systems, the size of the aperture is relevant because the diffraction pattern resulting from the aperture convolves to blurs out an image. The numerical aperture is defined as n sin theta. Where the angle is the angular size of the cone of light at the focal point.  

Diffraction phenomenon. There is a a pervading vague sense that diffraction and wave effects occur when the feature size of the slits or screen or thing are on the order of the wavelength of light. This isn't quite right

Huygens principle states that you can replicate the propagation of a wave by considering the superposition of point sources that are proportional to that value of the wave at all points.  

Roughly, a point source makes a field e Iomegar/ r  

In the far field limit, we can assume that z is much much larger than x or y.  

As a rough sketch of Hu

Just as point sources do not exist, neither do perfectly collimated beams. Any beam has finite diameter. This finite diameter is similar to putting the beam through a large hole, which would cause slight diffraction. The larger the hole, the less the diffraction, but it is always there.

Spatial coherence. In order to make a spatially incoherent source coherent, typically you pass it through a pinhole. The cittert van zernike theorem says how big the pinhole needs to be. The answer? Make the etendue connecting the source and pinhole roughly 1.  
Etendue also is very helpful for impossibility theorems and tricky machines. Why can you not take the light coming off a hot source and focus it to heat a target even hotter? Thermodynamics says you can't make energy spontaneously go from a colder object to a hotter one.  
Etendue is intimately related to entropy as it is very much the analog of classical phase space in mechanics. The entropy in statistical mechanics is the logarithm of the volume of phase space at a given energy.

[https://en.wikipedia.org/wiki/Abbe_sine_condition](https://en.wikipedia.org/wiki/Abbe_sine_condition)

Fourier Optics and the uncertainty principle

Sommerfeld had some interesting example in his book that gave me pause. I should look that up

